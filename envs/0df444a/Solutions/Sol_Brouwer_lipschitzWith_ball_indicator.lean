-- Prove2me | solution 1 for Brouwer.lipschitzWith_ball_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T00:31:01.599722+00:00
-- url     : https://prove2.me/submissions/92a3a848-ba04-4777-8edc-65301d828f4d

import Mathlib
import Theorems.Thm_Brouwer_norm_le_mul_dist_of_sphere_eq_zero

open Metric Set MeasureTheory

-- carved verbatim out of submission 08ed2756-557a-470f-8493-8c93e6b779c8, lines 51-67


theorem solution {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : NNReal) (hL : LipschitzOnWith L h (closedBall 0 1))
    (h0 : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, h x = 0) :
    LipschitzWith L ((closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).indicator h) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  by_cases hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 <;>
    by_cases hy : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    exact hL.dist_le_mul x hx y hy
  · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem hy, dist_zero_right]
    exact Brouwer.norm_le_mul_dist_of_sphere_eq_zero h L hL h0 hx hy
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem hy, dist_zero_left, dist_comm]
    exact Brouwer.norm_le_mul_dist_of_sphere_eq_zero h L hL h0 hy hx
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy, dist_self]
    positivity
