-- Prove2me | solution 1 for CircuitComplexity.Circuit.lower_bound_all_inputs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:15:21.750814+00:00
-- url     : https://prove2.me/submissions/0d29d94b-ae5d-4bf0-8bab-1bd2131e744a

module
public import Definitions.Def_LeanPool_CircuitComplexity_EssentialInput
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Sum
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_LowerBound
public import Theorems.Thm_CircuitComplexity_Circuit_essential_inputs_le_mul_size
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
    (c : Circuit (Basis.boundedAON k) N M G)
    (f : BitString N → BitString M)
    (hf : c.eval = f)
    (hall : ∀ i : Fin N, IsEssentialInput f i) :
    N ≤ k * c.size := by
  have hcard : (EssentialInputs f).card = N := by
    simp [EssentialInputs, Finset.filter_true_of_mem (fun i _ => hall i),
      Finset.card_univ, Fintype.card_fin]
  exact hcard.symm.trans_le (essential_inputs_le_mul_size c f hf)
end CircuitComplexity.Circuit
