-- Prove2me | solution 1 for CircuitComplexity.Circuit.essential_inputs_le_mul_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:33.053743+00:00
-- url     : https://prove2.me/submissions/6f4828f4-7275-43f9-9672-4696ad9c97e7

module
public import Definitions.Def_LeanPool_CircuitComplexity_EssentialInput
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Sum
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_LowerBound
public import Theorems.Thm_CircuitComplexity_Circuit_exists_gate_reads_input
public import Theorems.Thm_CircuitComplexity_Circuit_mem_coveredInputs
public import Theorems.Thm_CircuitComplexity_Circuit_boundedAON_coveredInputs_card_le
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth


section
@[expose] public section
namespace CircuitComplexity
namespace Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]
private theorem essential_subset_covered
    (c : Circuit B N M G) (f : BitString N → BitString M)
    (hf : c.eval = f) :
    EssentialInputs f ⊆ (Finset.univ : Finset (Fin G ⊕ Fin M)).biUnion
      (fun idx => coveredInputs (gateAt c idx)) := by
  intro i hi
  simp only [EssentialInputs, Finset.mem_filter] at hi
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  rcases exists_gate_reads_input c f hf i hi.2 with ⟨g, k, hk⟩ | ⟨j, k, hk⟩
  · exact ⟨.inl g, (mem_coveredInputs _ _).mpr ⟨k, hk⟩⟩
  · exact ⟨.inr j, (mem_coveredInputs _ _).mpr ⟨k, hk⟩⟩
end Circuit
end CircuitComplexity
end
end

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
    (hf : c.eval = f) :
    (EssentialInputs f).card ≤ k * c.size := by
  calc (EssentialInputs f).card
      ≤ ((Finset.univ : Finset (Fin G ⊕ Fin M)).biUnion
          (fun idx => coveredInputs (gateAt c idx))).card :=
        Finset.card_le_card (essential_subset_covered c f hf)
    _ ≤ ∑ idx : Fin G ⊕ Fin M,
          (coveredInputs (gateAt c idx)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _ : Fin G ⊕ Fin M, k :=
        Finset.sum_le_sum fun idx _ => boundedAON_coveredInputs_card_le _
    _ = (Fintype.card (Fin G ⊕ Fin M)) * k := by
        rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
    _ = k * c.size := by
        simp [Fintype.card_sum, Fintype.card_fin, size, Nat.mul_comm]
end CircuitComplexity.Circuit
