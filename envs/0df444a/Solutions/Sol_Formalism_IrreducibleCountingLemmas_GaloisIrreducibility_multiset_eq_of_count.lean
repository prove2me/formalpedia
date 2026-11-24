-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.multiset_eq_of_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:51:03.634442+00:00
-- url     : https://prove2.me/submissions/a5970357-afd2-4c7b-873b-84a0fca1f265

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
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_sum_mul_count_eq
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
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
theorem _root_.solution (s m : Multiset ℕ) (N : ℕ) (hs1 : ∀ d ∈ s, 1 ≤ d) (hs : s.sum = N)
    (hm1 : ∀ d ∈ m, 1 ≤ d) (hm : m.sum = N)
    (h : ∀ d ∈ Finset.Icc 2 N, s.count d = m.count d) : s = m := by
  ext d
  by_cases h2 : d ∈ Finset.Icc 2 N
  · exact h d h2
  by_cases h3 : d = 1 ∧ 1 ≤ N
  · obtain ⟨rfl, hN⟩ := h3
    have h1mem : 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩
    have e1 := Finset.add_sum_erase (Finset.Icc 1 N) (fun d => d * s.count d) h1mem
    have e2 := Finset.add_sum_erase (Finset.Icc 1 N) (fun d => d * m.count d) h1mem
    have e3 : ∑ x ∈ (Finset.Icc 1 N).erase 1, x * s.count x =
        ∑ x ∈ (Finset.Icc 1 N).erase 1, x * m.count x := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      obtain ⟨hne, hx'⟩ := Finset.mem_erase.mp hx
      rw [Finset.mem_Icc] at hx'
      rw [h x (Finset.mem_Icc.mpr ⟨by omega, hx'.2⟩)]
    beta_reduce at e1 e2
    rw [sum_mul_count_eq s N hs1 hs] at e1
    rw [sum_mul_count_eq m N hm1 hm] at e2
    simp only [one_mul] at e1 e2
    omega
  · have hout : ∀ t : Multiset ℕ, (∀ x ∈ t, 1 ≤ x) → t.sum = N → t.count d = 0 := by
      intro t ht1 hts
      rw [Multiset.count_eq_zero]
      intro hd
      have ha := ht1 d hd
      have hb := Multiset.le_sum_of_mem hd
      rw [hts] at hb
      rw [Finset.mem_Icc] at h2
      omega
    rw [hout s hs1 hs, hout m hm1 hm]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
