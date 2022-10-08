/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact cpFact = new CPFact();
        for (Var v : cfg.getIR().getParams()) {
            if (canHoldInt(v)) {
                cpFact.update(v, Value.getNAC());
            }
        }
        return cpFact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for (Var v : fact.keySet()) {
            target.update(v, meetValue(fact.get(v), target.get(v)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isNAC() || v2.isNAC())
            return Value.getNAC();
        if (v1.isUndef())
            return v2;
        if (v2.isUndef())
            return v1;
        if (v1.equals(v2))
            return v1;
        else
            return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact old_out = out.copy();

        out.copyFrom(in);

        if (! (stmt instanceof DefinitionStmt<?,?> definitionStmt))
            return ! out.equals(old_out);

        if (definitionStmt.getLValue() instanceof Var lvalue && canHoldInt(lvalue)) {
            out.remove(lvalue);
            RValue rvalue = definitionStmt.getRValue();
            if (rvalue instanceof Var var)
                out.update(lvalue, in.get(var));
            else if (rvalue instanceof IntLiteral intLiteral)
                out.update(lvalue, Value.makeConstant(intLiteral.getValue()));
            else if (rvalue instanceof BinaryExp binaryExp)
                out.update(lvalue, evaluate(binaryExp, in));
            else
                out.update(lvalue, Value.getNAC());
        }

        return ! out.equals(old_out);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me

        BinaryExp binaryExp = (BinaryExp) exp;
        Value v1 = in.get(binaryExp.getOperand1());
        Value v2 = in.get(binaryExp.getOperand2());

        // special case
        if (v2.isConstant()) {
            if (exp instanceof ArithmeticExp arithmeticExp && arithmeticExp.getOperator() == ArithmeticExp.Op.DIV) {
                if (v2.getConstant() == 0)
                    return Value.getUndef();
            }
            if (exp instanceof ArithmeticExp arithmeticExp && arithmeticExp.getOperator() == ArithmeticExp.Op.REM) {
                if (v2.getConstant() == 0)
                    return Value.getUndef();
            }
        }

        if (!v1.isConstant() || !v2.isConstant()) {
            if (v1.isNAC() || v2.isNAC())
                return Value.getNAC();
            return Value.getUndef();
        }

        if (exp instanceof ArithmeticExp arithmeticExp) {
            ArithmeticExp.Op op = arithmeticExp.getOperator();
            if (op == ArithmeticExp.Op.ADD)
                return Value.makeConstant(v1.getConstant() + v2.getConstant());
            if (op == ArithmeticExp.Op.SUB)
                return Value.makeConstant(v1.getConstant() - v2.getConstant());
            if (op == ArithmeticExp.Op.MUL)
                return Value.makeConstant(v1.getConstant() * v2.getConstant());
            if (op == ArithmeticExp.Op.DIV)
                return Value.makeConstant(v1.getConstant() / v2.getConstant());
            if (op == ArithmeticExp.Op.REM)
                return Value.makeConstant(v1.getConstant() % v2.getConstant());
        }

        if (exp instanceof ConditionExp conditionExp) {
            ConditionExp.Op op = conditionExp.getOperator();
            if (op == ConditionExp.Op.EQ && v1.getConstant() == v2.getConstant())
                return Value.makeConstant(1);
            if (op == ConditionExp.Op.NE && v1.getConstant() != v2.getConstant())
                return Value.makeConstant(1);
            if (op == ConditionExp.Op.LT && v1.getConstant() < v2.getConstant())
                return Value.makeConstant(1);
            if (op == ConditionExp.Op.GT && v1.getConstant() > v2.getConstant())
                return Value.makeConstant(1);
            if (op == ConditionExp.Op.LE && v1.getConstant() <= v2.getConstant())
                return Value.makeConstant(1);
            if (op == ConditionExp.Op.GE && v1.getConstant() >= v2.getConstant())
                return Value.makeConstant(1);
            return Value.makeConstant(0);
        }

        if (exp instanceof ShiftExp shiftExp) {
            ShiftExp.Op op = shiftExp.getOperator();
            if (op == ShiftExp.Op.SHL)
                return Value.makeConstant(v1.getConstant() << v2.getConstant());
            if (op == ShiftExp.Op.SHR)
                return Value.makeConstant(v1.getConstant() >> v2.getConstant());
            if (op == ShiftExp.Op.USHR)
                return Value.makeConstant(v1.getConstant() >>> v2.getConstant());
        }

        if (exp instanceof BitwiseExp bitwiseExp) {
            BitwiseExp.Op op = bitwiseExp.getOperator();
            if (op == BitwiseExp.Op.AND)
                return Value.makeConstant(v1.getConstant() & v2.getConstant());
            if (op == BitwiseExp.Op.OR)
                return Value.makeConstant(v1.getConstant() | v2.getConstant());
            if (op == BitwiseExp.Op.XOR)
                return Value.makeConstant(v1.getConstant() ^ v2.getConstant());
        }

        assert false;
        return null;
    }
}
