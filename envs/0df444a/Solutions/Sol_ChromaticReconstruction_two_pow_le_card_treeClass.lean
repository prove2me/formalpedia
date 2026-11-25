-- Prove2me | solution 1 for ChromaticReconstruction.two_pow_le_card_treeClass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:36:38.742602+00:00
-- url     : https://prove2.me/submissions/23211fac-360c-4226-bf79-576430b92952

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_CountingLower
import Theorems.Thm_ChromaticReconstruction_famTree_degree_iff
import Theorems.Thm_ChromaticReconstruction_exists_degree_iff_of_iso
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
attribute [local simp] ChromaticReconstruction.killP1_X_one
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inr
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inr



set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {k : ℕ} (hk : 3 ≤ k) :
    2 ^ (Nat.sqrt k - 2) ≤ Nat.card (TreeClass k) := by
  set m := Nat.sqrt k - 2 with hm
  have hmk : m * m + m + 3 ≤ k := by
    have h1 := Nat.sqrt_le' k
    rcases Nat.lt_or_ge (Nat.sqrt k) 2 with h | h
    · have : m = 0 := by omega
      rw [this]; omega
    · have : m + 2 = Nat.sqrt k := by omega
      nlinarith
  have hsum : ∀ A ∈ (Icc 1 m).powerset, ∑ i ∈ A, i ≤ m * m := by
    intro A hA
    rw [mem_powerset] at hA
    calc ∑ i ∈ A, i ≤ A.card • m := sum_le_card_nsmul _ _ _ fun i hi => (mem_Icc.1 (hA hi)).2
      _ ≤ m * m := by
        rw [smul_eq_mul]
        exact Nat.mul_le_mul_right _ ((card_le_card hA).trans (by simp))
  have hrange : ∀ A ∈ (Icc 1 m).powerset, A ⊆ range (k - 1 - ∑ i ∈ A, i) := by
    intro A hA i hi
    have := hsum A hA
    have := (mem_Icc.1 (mem_powerset.1 hA hi)).2
    rw [mem_range]
    omega
  let cls : {A // A ∈ (Icc 1 m).powerset} → TreeClass k := fun A =>
    Quotient.mk _ (famTreeFin k A.1 (hrange A.1 A.2) (by have := hsum A.1 A.2; omega))
  have hinj : Function.Injective cls := by
    rintro ⟨A, hA⟩ ⟨B, hB⟩ h
    obtain ⟨e⟩ := Quotient.exact h
    simp only [famTreeFin] at e
    have e' := ((SimpleGraph.Iso.map _ _).trans e).trans (SimpleGraph.Iso.map _ _).symm
    apply Subtype.ext
    simp only
    ext i
    by_cases hi : i ∈ Icc 1 m
    · rw [mem_Icc] at hi
      have hrA : m + 2 ≤ k - 1 - ∑ i ∈ A, i := by have := hsum A hA; omega
      have hrB : m + 2 ≤ k - 1 - ∑ i ∈ B, i := by have := hsum B hB; omega
      rw [← famTree_degree_iff hrA hi.1 hi.2, ← famTree_degree_iff hrB hi.1 hi.2]
      exact exists_degree_iff_of_iso e' _
    · constructor
      · intro h'; exact absurd (mem_powerset.1 hA h') hi
      · intro h'; exact absurd (mem_powerset.1 hB h') hi
  have := Nat.card_le_card_of_injective cls hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_powerset, Nat.card_Icc,
    Nat.add_sub_cancel] at this
  exact this
end ChromaticReconstruction
