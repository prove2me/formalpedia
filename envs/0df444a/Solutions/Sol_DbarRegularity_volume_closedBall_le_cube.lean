-- Prove2me | solution 1 for DbarRegularity.volume_closedBall_le_cube
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T23:52:21.919978+00:00
-- url     : https://prove2.me/submissions/2e283405-09b6-4277-9e4a-7d175b3ed3be

import Definitions.Def_DbarRegularity_Setting
import Theorems.Thm_DbarRegularity_volume_closedCube



namespace DbarRegularity

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal NNReal

theorem volume_closedBall_le_cube {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) {ρ : ℝ} :
    volume (closedBall x ρ) ≤ ENNReal.ofReal (2 * ρ) ^ d := by
  rw [← volume_closedCube (WithLp.toLp 2 fun i => x i - ρ)]
  refine measure_mono fun y hy i => ?_
  have h := (PiLp.dist_apply_le y x i).trans (mem_closedBall.1 hy)
  rw [Real.dist_eq, abs_le] at h
  simp only [PiLp.toLp_apply]
  constructor <;> linarith

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric
open scoped ENNReal

theorem solution {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) {ρ : ℝ} :
    volume (closedBall x ρ) ≤ ENNReal.ofReal (2 * ρ) ^ d :=
  volume_closedBall_le_cube x
