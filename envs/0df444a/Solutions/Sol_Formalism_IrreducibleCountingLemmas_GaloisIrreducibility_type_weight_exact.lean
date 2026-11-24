-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.type_weight_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:00:52.875187+00:00
-- url     : https://prove2.me/submissions/6148a66e-8b89-4208-a98f-54bb69f7d67e

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
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_sqWeight_eq
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_one_le_of_mem_degType
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_mem_sqSet
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_monic
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_natDegree
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_type_count_exact
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
open scoped ComplexOrder
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : TypeWeightExact := by
  intro K _ _ N n hn
  set q : ℝ := (Fintype.card K : ℝ) with hq
  have hconst : ∀ c : Fin N → K,
      (∀ d ∈ Finset.Icc 1 N, (degType (monicOf c)).count d = n d) →
      sqWeight (monicOf c) = ∏ d ∈ Finset.Icc 1 N, ((q ^ d - 1)⁻¹) ^ (n d) := by
    intro c hcount
    rw [sqWeight_eq, Finset.prod_multiset_map_count]
    have hsub : (degType (monicOf c)).toFinset ⊆ Finset.Icc 1 N := by
      intro d hd
      have hd' := Multiset.mem_toFinset.mp hd
      refine Finset.mem_Icc.mpr ⟨one_le_of_mem_degType _ d hd', ?_⟩
      have h1 := Multiset.le_sum_of_mem hd'
      rwa [sum_degType _ (monicOf_monic c).ne_zero, monicOf_natDegree] at h1
    rw [Finset.prod_subset hsub]
    · exact Finset.prod_congr rfl fun d hd => by rw [hcount d hd]
    · intro d _ hd
      rw [Multiset.count_eq_zero_of_notMem (fun h => hd (Multiset.mem_toFinset.mpr h)), pow_zero]
  refine (Finset.sum_congr rfl (fun c hc => by
    simp only [Finset.mem_filter] at hc
    exact hconst c hc.2)).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard := type_count_exact K N n hn
  have key : ∀ a : ℕ → ℕ, (∏ d ∈ Finset.Icc 1 N, ((a d : ℕ) : ℝ) / (q ^ d - 1) ^ (n d)) =
      ((∏ d ∈ Finset.Icc 1 N, a d : ℕ) : ℝ) * ∏ d ∈ Finset.Icc 1 N, ((q ^ d - 1)⁻¹) ^ (n d) := by
    intro a
    rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun d _ => by rw [inv_pow, div_eq_mul_inv]
  rw [key, ← hcard]
  congr 3
  ext c
  simp only [Finset.mem_filter, mem_sqSet, Finset.mem_univ, true_and, and_assoc]
  rfl
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
