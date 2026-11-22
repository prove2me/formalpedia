-- Prove2me | solution 1 for CircuitComplexity.AONOp.eval_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:43.2535+00:00
-- url     : https://prove2.me/submissions/72746267-bf96-4cea-9fd2-06e107301fc7

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
theorem _root_.solution (op : AONOp) (v : Fin 1 → Bool) :
    op.eval 1 v = op.binOp op.identity (v 0) := by
  cases op <;> simp [AONOp.eval, AONOp.binOp, AONOp.identity, Fin.foldl_succ_last, Fin.foldl_zero]
end AONOp
end CircuitComplexity
