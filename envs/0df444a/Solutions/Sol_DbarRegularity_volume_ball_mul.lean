-- Prove2me | solution 1 for DbarRegularity.volume_ball_mul
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T23:22:33.916526+00:00
-- url     : https://prove2.me/submissions/158067ba-55a8-42d3-aa78-30bae578f191

import Definitions.Def_DbarRegularity_Setting



namespace DbarRegularity

open MeasureTheory Metric Set
open scoped ENNReal NNReal

/-- Scaling of ball volumes in `ℝ^d`. -/
theorem volume_ball_mul (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) (c : ℝ)
    (hc : 0 < c) :
    volume (ball x (c * r)) = ENNReal.ofReal c ^ d * volume (ball x r) := by
  rw [Measure.addHaar_ball_of_pos _ _ (by positivity), Measure.addHaar_ball_of_pos _ _ hr,
    finrank_euclideanSpace_fin, mul_pow, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow hc.le, mul_assoc]

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric
open scoped ENNReal NNReal

theorem solution (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) (c : ℝ)
    (hc : 0 < c) :
    volume (ball x (c * r)) = ENNReal.ofReal c ^ d * volume (ball x r) :=
  volume_ball_mul d x hr c hc
