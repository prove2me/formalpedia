-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.comparison_transfer_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:52.472285+00:00
-- url     : https://prove2.me/submissions/3be6d3b8-6258-4d51-b38f-52f31cb53b75

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
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : ComparisonTransfer := by
  intro ι _ _ T _ wU wJ g A hg hU0 hU1 hJ1 hJU
  classical
  have hg0 : 0 < g := by linarith
  have hgi : 1 / g ≤ 1 := (div_le_one hg0).2 hg
  have hgi0 : 0 ≤ 1 / g := by positivity
  set a : ℝ := 1 - 1 / g with ha
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have ha1 : a ≤ 1 := by rw [ha]; linarith
  have htot : ∀ w : ∀ v, T v → ℝ, (∀ v, ∑ t, w v t = 1) →
      ∑ x : (∀ v, T v), ∏ v, w v (x v) = 1 := by
    intro w hw
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
    simp [hw]
  have hprod : ∀ x : (∀ v, T v), a ^ Fintype.card ι * ∏ v, wU v (x v) ≤ ∏ v, wJ v (x v) := by
    intro x
    rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun v _ => mul_nonneg ha0 (hU0 v _)) (fun v _ => hJU v _)
  have hsJ := Finset.sum_sdiff (f := fun x => ∏ v, wJ v (x v)) (Finset.subset_univ A)
  have hsU := Finset.sum_sdiff (f := fun x => ∏ v, wU v (x v)) (Finset.subset_univ A)
  rw [htot wJ hJ1] at hsJ
  rw [htot wU hU1] at hsU
  have hcomp : a ^ Fintype.card ι * ∑ x ∈ Finset.univ \ A, ∏ v, wU v (x v) ≤
      ∑ x ∈ Finset.univ \ A, ∏ v, wJ v (x v) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun x _ => hprod x)
  have hA0 : 0 ≤ ∑ x ∈ A, ∏ v, wU v (x v) :=
    Finset.sum_nonneg (fun x _ => Finset.prod_nonneg (fun v _ => hU0 v _))
  have hbern : 1 - (Fintype.card ι : ℝ) / g ≤ a ^ Fintype.card ι := by
    have h := one_add_mul_le_pow (a := -(1 / g)) (by linarith) (Fintype.card ι)
    have e1 : 1 + (Fintype.card ι : ℝ) * -(1 / g) = 1 - (Fintype.card ι : ℝ) / g := by ring
    have e2 : 1 + -(1 / g) = a := by rw [ha]; ring
    rw [e1, e2] at h
    exact h
  have hpow1 : a ^ Fintype.card ι ≤ 1 := pow_le_one₀ ha0 ha1
  have hc : ∑ x ∈ Finset.univ \ A, ∏ v, wU v (x v) = 1 - ∑ x ∈ A, ∏ v, wU v (x v) := by linarith
  rw [hc] at hcomp
  have hm := mul_le_mul_of_nonneg_right hpow1 hA0
  nlinarith
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
