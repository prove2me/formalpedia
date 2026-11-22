-- Prove2me | solution 1 for CircuitComplexity.AONOp.binOp_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:36.660799+00:00
-- url     : https://prove2.me/submissions/436d5ac8-6232-468c-b514-fc2391bc4678

module
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_AON
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Simulation

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
namespace CircuitComplexity
namespace AONOp
theorem _root_.solution (op : AONOp) (b : Bool) : op.binOp b b = b := by
  cases op <;> cases b <;> rfl
end AONOp
end CircuitComplexity
