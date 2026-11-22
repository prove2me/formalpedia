-- Prove2me | solution 1 for CircuitComplexity.AONOp.eval_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:40.305777+00:00
-- url     : https://prove2.me/submissions/cb00d504-6208-4db4-a6ff-6d034354878f

module
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_AON
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Simulation
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth



set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
namespace CircuitComplexity
namespace AONOp
theorem _root_.solution (op : AONOp) : op.eval 0 Fin.elim0 = op.identity := by
  cases op <;> simp [AONOp.eval, AONOp.identity, Fin.foldl_zero]
end AONOp
end CircuitComplexity
