-- Prove2me | solution 1 for CircuitComplexity.Circuit.mem_coveredInputs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:10:16.490351+00:00
-- url     : https://prove2.me/submissions/e46d17e2-8ffb-4435-920f-82f4e568fae3

module
public import Definitions.Def_LeanPool_CircuitComplexity_EssentialInput
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Sum
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_LowerBound
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth



set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]
omit [NeZero N]
namespace CircuitComplexity.Circuit
theorem _root_.solution (g : Gate B (N + G)) (i : Fin N) :
    i ∈ coveredInputs g ↔ ∃ k : Fin g.fanIn, (g.inputs k).val = i.val := by
  simp [coveredInputs]
end CircuitComplexity.Circuit
