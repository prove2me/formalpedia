-- Prove2me | solution 1 for CircuitComplexity.AONOp.binOp_assoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:37.178057+00:00
-- url     : https://prove2.me/submissions/80c71662-096a-47af-b404-4aee3efdbdf9

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
theorem _root_.solution (op : AONOp) (a b c : Bool) :
    op.binOp (op.binOp a b) c = op.binOp a (op.binOp b c) := by
  cases op <;> simp [AONOp.binOp, Bool.and_assoc, Bool.or_assoc]
end AONOp
end CircuitComplexity
