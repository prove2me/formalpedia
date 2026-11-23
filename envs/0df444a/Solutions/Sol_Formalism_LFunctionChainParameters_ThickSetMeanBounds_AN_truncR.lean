-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN.truncR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:52.948807+00:00
-- url     : https://prove2.me/submissions/bdf795c9-ccd3-453f-a62f-16aa4c13ead8

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.ThickSetMeanBounds
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData
open Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN
namespace Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN
theorem _root_.solution (c : ℕ → ℝ) (y : ℝ) (M : ℕ) (hM : ⌊y⌋₊ ≤ M) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, c n * (y / n - 1) = ∑ n ∈ Icc 1 M, c n * (max (y / n - 1) 0) := by
  have h1 : ∑ n ∈ Icc 1 ⌊y⌋₊, c n * (max (y / n - 1) 0) = ∑ n ∈ Icc 1 M, c n * (max (y / n - 1) 0) := by
    apply Finset.sum_subset (Finset.Icc_subset_Icc_right hM)
    intro n hn hn'
    rw [Finset.mem_Icc] at hn hn'
    have hlt : ⌊y⌋₊ < n := by
      by_contra h; exact hn' ⟨hn.1, not_lt.1 h⟩
    have hy : y < n := (Nat.floor_lt' (by omega)).1 hlt
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have : y / n - 1 ≤ 0 := by
      have := (div_lt_one hn0).2 hy; linarith
    rw [max_eq_right this]; simp
  rw [← h1]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_Icc] at hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
  have hy : (n : ℝ) ≤ y := (Nat.le_floor_iff' (by omega)).1 hn.2
  have : 0 ≤ y / n - 1 := by
    have := (one_le_div hn0).2 hy; linarith
  rw [max_eq_left this]
end Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN
