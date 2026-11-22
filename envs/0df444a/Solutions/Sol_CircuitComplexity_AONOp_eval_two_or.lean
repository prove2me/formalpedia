-- Prove2me | solution 1 for CircuitComplexity.AONOp.eval_two_or
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:12.000435+00:00
-- url     : https://prove2.me/submissions/95293e69-7844-4ba3-a03a-64ee8e5c2c3c

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth



set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
namespace CircuitComplexity
namespace AONOp
theorem _root_.solution (inputs : BitString 2) :
    AONOp.eval .or 2 inputs = (inputs 0 || inputs 1) := by
  simp [AONOp.eval, Fin.foldl_succ_last, Fin.foldl_zero]
end AONOp
end CircuitComplexity
