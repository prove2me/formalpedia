-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.type_set_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:16:51.672856+00:00
-- url     : https://prove2.me/submissions/02bf0042-cb34-4136-8f33-638d1e8d04d0

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_PropositionOneCentralCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRDivisorDegreeSubSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleProbSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaLWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartEqIff
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartSpec
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdemSelfAdjoint
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSquarefreeCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRTypeCountExact
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleTypeProb
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_sum_degType
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_one_le_of_mem_degType
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_sqWeight_nonneg
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_type_weight_le
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_monic
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_natDegree
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
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : TypeSetWeight := by
  classical
  intro K _ _ N A
  set T : Finset (Multiset ℕ) := (Finset.univ : Finset N.Partition).image (fun p => p.parts)
    with hT
  have hTmem : ∀ m : Multiset ℕ, (∀ d ∈ m, 1 ≤ d) → m.sum = N → m ∈ T := by
    intro m h1 h2
    exact Finset.mem_image.mpr ⟨⟨m, fun {i} hi => h1 i hi, h2⟩, Finset.mem_univ _, rfl⟩
  have hTprop : ∀ m ∈ T, (∀ d ∈ m, 1 ≤ d) ∧ m.sum = N := by
    intro m hm
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hm
    exact ⟨fun d hd => p.parts_pos hd, p.parts_sum⟩
  have hfac : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast N.factorial_pos
  rw [← Finset.sum_fiberwise_of_maps_to (t := T) (g := fun c => degType (monicOf c))
    (fun c _ => hTmem _ (one_le_of_mem_degType _)
      (by rw [sum_degType _ (monicOf_monic c).ne_zero, monicOf_natDegree]))]
  rw [Finset.card_eq_sum_card_fiberwise (t := T) (f := fun σ : Equiv.Perm (Fin N) => σ.partition.parts)
    (fun σ _ => hTmem _ (fun d hd => σ.partition.parts_pos hd)
      (by rw [σ.partition.parts_sum, Fintype.card_fin]))]
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_le_sum
  intro m hm
  obtain ⟨hm1, hm2⟩ := hTprop m hm
  by_cases hA : A m
  · refine le_trans ?_ (le_trans (type_weight_le K N m hm1 hm2) ?_)
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro c hc
        simp only [Finset.mem_filter] at hc ⊢
        exact ⟨hc.1.1, hc.2⟩
      · intro c _ _
        exact sqWeight_nonneg _
    · apply div_le_div_of_nonneg_right _ hfac.le
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      exact ⟨hσ ▸ hA, hσ⟩
  · rw [Finset.sum_eq_zero]
    · positivity
    · intro c hc
      simp only [Finset.mem_filter] at hc
      exact absurd (hc.2 ▸ hc.1.2) hA
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
