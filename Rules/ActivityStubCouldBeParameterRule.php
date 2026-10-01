<?php

declare(strict_types=1);

namespace Gplanchat\Durable\PHPStan\Rules;

use Gplanchat\Durable\Attribute\AsWorkflowMethod;
use PhpParser\Node;
use PhpParser\Node\Expr;
use PhpParser\Node\Expr\ArrowFunction;
use PhpParser\Node\Expr\Assign;
use PhpParser\Node\Expr\ClassConstFetch;
use PhpParser\Node\Expr\Closure;
use PhpParser\Node\Expr\MethodCall;
use PhpParser\Node\Expr\NullsafePropertyFetch;
use PhpParser\Node\Expr\PropertyFetch;
use PhpParser\Node\Expr\Variable;
use PhpParser\Node\Identifier;
use PhpParser\Node\Name;
use PhpParser\Node\Stmt\Class_;
use PhpParser\Node\Stmt\ClassMethod;
use PhpParser\Node\Stmt\Expression;
use PhpParser\NodeFinder;
use PHPStan\Analyser\Scope;
use PHPStan\Node\InClassNode;
use PHPStan\Rules\IdentifierRuleError;
use PHPStan\Rules\Rule;
use PHPStan\Rules\RuleErrorBuilder;

/**
 * Reports an activity stub built with `$env->activityStub(Contract::class, …)` that could be an
 * `#[Activities(Contract::class, …)]` parameter of the workflow method instead.
 *
 * A report, not a rewrite: the developer moves it by hand, so a rare false positive is tolerable.
 * The rule still stays silent wherever the move would change what runs:
 *
 * - options that are not literals, or literals the attribute cannot carry with the same meaning:
 *   `default()` or an `of()` that sets nothing (the attribute would then build the stub with no
 *   options, and the Durable worker would retry with no backoff), an empty `taskQueue` (which the
 *   attribute refuses), an `activityId`, or values the attribute refuses at registration;
 * - a stub read anywhere but one workflow method, or inside a closure;
 * - a class that extends another, implements an interface or uses a trait: one of them may
 *   declare or call the workflow method, which then cannot gain a required parameter.
 *
 * @implements Rule<InClassNode>
 */
final class ActivityStubCouldBeParameterRule implements Rule
{
    public const IDENTIFIER = 'durable.activityStubCouldBeParameter';

    private const TIP = 'Keep activityStub() when the options are computed at run time, or when a signal, update or helper method, or a closure, uses the stub. Otherwise ignore this with the identifier ' . self::IDENTIFIER . '.';

    public function getNodeType(): string
    {
        return InClassNode::class;
    }

    /**
     * @return list<IdentifierRuleError>
     */
    public function processNode(Node $node, Scope $scope): array
    {
        $class = $node->getOriginalNode();
        // An interface, a parent or a trait may declare the workflow method, which then cannot
        // gain a required parameter, or call it without the stub.
        if (!$class instanceof Class_ || null !== $class->extends || [] !== $class->implements || [] !== $class->getTraitUses()) {
            return [];
        }

        $workflowMethods = [];
        foreach ($class->getMethods() as $method) {
            if (self::isWorkflowMethod($method)) {
                $workflowMethods[$method->name->toLowerString()] = $method;
            }
        }
        if ([] === $workflowMethods) {
            return [];
        }

        $errors = [];
        // A stub built in the workflow method itself, into a local variable.
        foreach ($workflowMethods as $method) {
            foreach ($method->stmts ?? [] as $stmt) {
                if ($stmt instanceof Expression && $stmt->expr instanceof Assign
                    && $stmt->expr->var instanceof Variable && \is_string($stmt->expr->var->name)) {
                    $errors[] = self::report($stmt->expr->expr, $stmt->expr->var->name, $method);
                }
            }
        }
        // A stub built in the constructor, into a property only one workflow method reads.
        foreach ($class->getMethod('__construct')->stmts ?? [] as $stmt) {
            if ($stmt instanceof Expression && $stmt->expr instanceof Assign
                && $stmt->expr->var instanceof PropertyFetch && self::isThis($stmt->expr->var->var)
                && $stmt->expr->var->name instanceof Identifier) {
                $name = $stmt->expr->var->name->toString();
                $reader = self::onlyReader($class, $name);
                if (null !== $reader && isset($workflowMethods[$reader])) {
                    $errors[] = self::report($stmt->expr->expr, $name, $workflowMethods[$reader]);
                }
            }
        }

        return array_values(array_filter($errors));
    }

    private static function report(Expr $call, string $name, ClassMethod $method): ?IdentifierRuleError
    {
        if (!$call instanceof MethodCall || !$call->name instanceof Identifier || 'activityStub' !== $call->name->toString()) {
            return null;
        }
        $args = $call->getArgs();
        $contract = $args[0]->value ?? null;
        if (\count($args) !== \count($call->args) || \count($args) > 2 || null !== ($args[0]->name ?? null)
            || !$contract instanceof ClassConstFetch || !$contract->class instanceof Name
            || !$contract->name instanceof Identifier || 'class' !== $contract->name->toLowerString()) {
            return null;
        }
        // Options are not mapped to attribute fields yet.
        if (isset($args[1])) {
            return null;
        }

        $short = $contract->class->getLast();
        $attribute = $short . '::class';

        return RuleErrorBuilder::message(\sprintf(
            'Activity stub $%2$s could be a parameter of %1$s(): #[Activities(%3$s)] ActivityStub $%2$s, documented with @param ActivityStub<%4$s> $%2$s.',
            $method->name->toString(),
            $name,
            $attribute,
            $short,
        ))
            ->identifier(self::IDENTIFIER)
            ->tip(self::TIP)
            ->line($call->getStartLine())
            ->build();
    }

    /**
     * The lower-cased name of the one method that reads `$this->{$name}`, or null when none does,
     * when several do, when a closure does, or when the property may be reached another way.
     */
    private static function onlyReader(Class_ $class, string $name): ?string
    {
        $finder = new NodeFinder();
        $reads = static fn(Node $n): bool => ($n instanceof PropertyFetch || $n instanceof NullsafePropertyFetch)
            && (!$n->name instanceof Identifier || $name === $n->name->toString());
        $readers = [];
        foreach ($class->getMethods() as $method) {
            if ('__construct' === $method->name->toLowerString() || null === $finder->findFirst($method->stmts ?? [], $reads)) {
                continue;
            }
            foreach ($finder->find($method->stmts ?? [], static fn(Node $n): bool => $n instanceof Closure || $n instanceof ArrowFunction || $n instanceof Class_) as $nested) {
                if (null !== $finder->findFirst([$nested], $reads)) {
                    return null;
                }
            }
            $readers[] = $method->name->toLowerString();
        }

        return 1 === \count($readers) ? $readers[0] : null;
    }

    private static function isThis(Expr $expr): bool
    {
        return $expr instanceof Variable && 'this' === $expr->name;
    }

    private static function isWorkflowMethod(ClassMethod $method): bool
    {
        foreach ($method->attrGroups as $group) {
            foreach ($group->attrs as $attribute) {
                if (AsWorkflowMethod::class === $attribute->name->toString()) {
                    return true;
                }
            }
        }

        return false;
    }
}
