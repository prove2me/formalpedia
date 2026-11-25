-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.series_bounds_hold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:06:28.92548+00:00
-- url     : https://prove2.me/submissions/e9b826ca-56ed-41a8-83f1-09067089707f

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
theorem _root_.solution : SeriesBounds := by
  intro u N hu0 hu8
  constructor
  · rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 2), Finset.sum_empty]
      positivity
    · have key : ∀ n, 1 ≤ n → ∑ δ ∈ Finset.Icc (2 : ℕ) n, ((δ : ℕ) : ℝ) * u ^ δ +
          u ^ (n + 1) * (8 / 7 * (n : ℝ) + 64 / 49) ≤ 6 * u ^ 2 := by
        intro n hn
        induction n, hn using Nat.le_induction with
        | base =>
          simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (1 : ℕ) < 2), Finset.sum_empty]
          norm_num
          nlinarith [sq_nonneg u]
        | succ n hn ih =>
          rw [Finset.sum_Icc_succ_top (by omega)]
          push_cast at ih ⊢
          have hun : 0 ≤ u ^ (n + 1) := pow_nonneg hu0 _
          have hp : 0 ≤ 8 / 7 * ((n : ℝ) + 1) + 64 / 49 := by positivity
          have hw : u ^ (n + 1 + 1) = u ^ (n + 1) * u := pow_succ _ _
          rw [hw]
          nlinarith [mul_nonneg (mul_nonneg hun hp) (sub_nonneg.2 hu8)]
      have h1 := key N hN
      have h2 : 0 ≤ u ^ (N + 1) * (8 / 7 * (N : ℝ) + 64 / 49) := by positivity
      linarith
  · have key : ∀ n, ∑ δ ∈ Finset.Icc (1 : ℕ) n, ((δ : ℕ) : ℝ) ^ 2 * u ^ δ +
        u ^ (n + 1) * (8 / 7 * (n : ℝ) ^ 2 + 128 / 49 * n + 576 / 343) ≤ 17 / 10 * u := by
      intro n
      induction n with
      | zero =>
        simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1), Finset.sum_empty]
        norm_num
        nlinarith
      | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by omega)]
        push_cast at ih ⊢
        have hun : 0 ≤ u ^ (n + 1) := pow_nonneg hu0 _
        have hp : 0 ≤ 8 / 7 * ((n : ℝ) + 1) ^ 2 + 128 / 49 * ((n : ℝ) + 1) + 576 / 343 := by
          positivity
        have hw : u ^ (n + 1 + 1) = u ^ (n + 1) * u := pow_succ _ _
        rw [hw]
        nlinarith [mul_nonneg (mul_nonneg hun hp) (sub_nonneg.2 hu8)]
    have h1 := key N
    have h2 : 0 ≤ u ^ (N + 1) * (8 / 7 * (N : ℝ) ^ 2 + 128 / 49 * N + 576 / 343) := by positivity
    linarith
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
