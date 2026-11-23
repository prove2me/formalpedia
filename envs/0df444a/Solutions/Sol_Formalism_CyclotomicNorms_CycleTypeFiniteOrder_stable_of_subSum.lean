-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.stable_of_subSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:40.199244+00:00
-- url     : https://prove2.me/submissions/e06e34ee-6053-4b07-846f-bfb67fd90aca

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_mem_cyc
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_blocks_disjoint
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_exists_le_map
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_SubsetSumInvariance_exists_le_map
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {α K : Type*} [Fintype α] [DecidableEq α] [DecidableEq K] [Monoid K]
variable (σ : Equiv.Perm α) (L : α → K)
variable {σ L}
namespace Formalism.CyclotomicNorms.CycleTypeFiniteOrder
theorem _root_.solution (hLi : Function.Injective L) {a : ℕ}
    (h : Formalism.GaloisIrreducibility.IsSubSum ((blocks σ L).val.map Finset.card) a) :
    ∃ A : Finset α, (∀ i ∈ A, σ i ∈ A) ∧ A.card = a := by
  obtain ⟨s, hs, hsum⟩ := h
  obtain ⟨t, ht, rfl⟩ := exists_le_map _ _ _ hs
  set T : Finset (Finset K) := ⟨t, Multiset.nodup_of_le ht (blocks σ L).nodup⟩
  have hTsub : ∀ S ∈ T, S ∈ blocks σ L := fun S hS => Multiset.mem_of_le ht hS
  refine ⟨Finset.univ.filter (fun i => ∃ S ∈ T, L i ∈ S), ?_, ?_⟩
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    obtain ⟨S, hST, hiS⟩ := hi
    refine ⟨S, hST, ?_⟩
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (hTsub S hST)
    obtain ⟨k, hk, hki⟩ := Finset.mem_image.mp hiS
    rw [hLi hki] at hk
    exact Finset.mem_image_of_mem _ (mem_cyc.mpr (Equiv.Perm.sameCycle_apply_right.mpr (mem_cyc.mp hk)))
  · rw [← Finset.card_image_of_injective _ hLi]
    have himg : (Finset.univ.filter (fun i => ∃ S ∈ T, L i ∈ S)).image L = T.biUnion id := by
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_biUnion, id]
      constructor
      · rintro ⟨i, ⟨S, hS, hiS⟩, rfl⟩; exact ⟨S, hS, hiS⟩
      · rintro ⟨S, hS, hx⟩
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (hTsub S hS)
        obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
        exact ⟨k, ⟨_, hS, hx⟩, rfl⟩
    rw [himg, show T.biUnion id = T.biUnion (fun S => S) from rfl, Finset.card_biUnion (fun S hS T' hT' h =>
      blocks_disjoint hLi (hTsub S hS) (hTsub T' hT') h), ← hsum]
    rfl
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
