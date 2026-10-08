-- Prove2me | solution 1 for ConvexOptAlg.Newton.lipschitz_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:36:12.981346+00:00
-- url     : https://prove2.me/submissions/9d6864d7-49d0-4c4c-a923-5fffe78d0611

import Mathlib
import Definitions.Def_ConvexOptAlg_Newton_Defs

open ConvexOptAlg.Newton in
theorem solution {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (M : ℝ) (hHL : IsLipschitzHessian H M) (xstar y : EuclideanSpace ℝ (Fin n)) :
    ∫ s in (0 : ℝ)..1, ‖H y - H (xstar + s • (y - xstar))‖ ≤ M / 2 * ‖y - xstar‖ := by
  have hLip : LipschitzWith (Real.toNNReal M) H := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal']
    calc ‖H a - H b‖ ≤ M * ‖a - b‖ := hHL a b
      _ ≤ max M 0 * ‖a - b‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hcont : Continuous fun s : ℝ => ‖H y - H (xstar + s • (y - xstar))‖ := by
    have : Continuous fun s : ℝ => xstar + s • (y - xstar) := by fun_prop
    exact (continuous_const.sub (hLip.continuous.comp this)).norm
  have hpt : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖H y - H (xstar + s • (y - xstar))‖ ≤ M * ‖y - xstar‖ * (1 - s) := by
    intro s hs
    have h1 := hHL y (xstar + s • (y - xstar))
    have h2 : y - (xstar + s • (y - xstar)) = (1 - s) • (y - xstar) := by
      rw [sub_smul, one_smul]; abel
    rw [h2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2])] at h1
    linarith
  have hle := intervalIntegral.integral_mono_on (zero_le_one' ℝ)
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 1) ((by fun_prop : Continuous fun s : ℝ =>
      M * ‖y - xstar‖ * (1 - s)).intervalIntegrable (μ := MeasureTheory.volume) 0 1) hpt
  have hval : ∫ s in (0 : ℝ)..1, M * ‖y - xstar‖ * (1 - s) = M / 2 * ‖y - xstar‖ := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    simp
    ring
  linarith
