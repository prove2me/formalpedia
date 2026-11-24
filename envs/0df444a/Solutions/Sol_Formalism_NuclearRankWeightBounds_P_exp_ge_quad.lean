-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.exp_ge_quad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:11:16.910791+00:00
-- url     : https://prove2.me/submissions/d568236d-0978-4cdf-9a96-32b7b1cab4e3

import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_LogSumExpBoundHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Finset
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution {z : ℝ} (hz : |z| ≤ 1) : 1 + z + z ^ 2 / 3 ≤ Real.exp z := by
  rcases le_or_gt 0 z with h0 | h0
  · have := Real.quadratic_le_exp_of_nonneg h0
    nlinarith [sq_nonneg z]
  · have h := Real.exp_bound hz (n := 5) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h
    have h2 := (abs_le.mp h).1
    have ha : |z| = -z := abs_of_neg h0
    rw [ha] at h2 hz
    have hz1 : -1 ≤ z := by linarith
    nlinarith [sq_nonneg z, mul_nonneg (mul_nonneg (sq_nonneg z) (by linarith : (0:ℝ) ≤ z + 1)) (by linarith : (0:ℝ) ≤ -z),
      pow_two_nonneg (z ^ 2), mul_nonneg (sq_nonneg z) (by linarith : (0:ℝ) ≤ z + 1),
      mul_nonneg (mul_nonneg (sq_nonneg z) (sq_nonneg z)) (by linarith : (0:ℝ) ≤ z + 1)]
end Formalism.NuclearRankWeightBounds.P
