-- Prove2me | solution 1 for CircuitComplexity.Circuit.boundedAON_coveredInputs_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:30.121012+00:00
-- url     : https://prove2.me/submissions/9733e0a2-2ad8-4f5e-a7fd-181add9e9bc3

module
public import Definitions.Def_LeanPool_CircuitComplexity_EssentialInput
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Sum
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_LowerBound
public import Theorems.Thm_CircuitComplexity_Circuit_card_coveredInputs_le
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth



set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]
namespace CircuitComplexity.Circuit
theorem _root_.solution {k : Nat}
    (g : Gate (Basis.boundedAON k) (N + G)) :
    (coveredInputs g : Finset (Fin N)).card ≤ k := by
  have hfanIn : g.fanIn ≤ k := by
    have h := g.arityOk
    revert h; cases g.op <;> simp [Basis.boundedAON, Arity.satisfiedBy]
  exact le_trans (card_coveredInputs_le g) hfanIn
end CircuitComplexity.Circuit
