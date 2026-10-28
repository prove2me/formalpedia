-- Prove2me | solution 1 for FunctionalInequalities.Energy.lipschitzOnWith_mollify_ball_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:44:29.094796+00:00
-- url     : https://prove2.me/submissions/55fb399b-fa48-4fae-a67e-f7935386d5b6

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Recovery

noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff
universe u
section Mollification
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
omit [CompleteSpace V] [SecondCountableTopology V] in
/-- The mollification at radius `R` inherits, on the ball of radius `δ`, every Lipschitz constant
of `g` on the ball of radius `δ + 2 * R`: the kernel of radius `2 * R` sees nothing further. -/
theorem solution (m : Measure V) [m.IsAddHaarMeasure]
    {R δ : ℝ} (hR : 0 < R) {c : ℝ≥0} {g : V → ℝ} (hg : Continuous g) (x : V)
    (h : LipschitzOnWith c g (Metric.ball x (δ + 2 * R))) :
    LipschitzOnWith c (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.mollify m R g) (Metric.ball x δ) := by
  refine LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ ?_
  have hyx : ‖y - x‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hy
  have hzx : ‖z - x‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  rw [FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.mollify_apply, FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.mollify_apply, Real.dist_eq,
    ← integral_sub (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.integrable_shift_mul_kernel m hR hg y) (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.integrable_shift_mul_kernel m hR hg z)]
  have hKint : Integrable (fun t ↦ (c : ℝ) * dist y z * FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.kernel m R t) m :=
    (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.integrable_kernel m hR).const_mul _
  calc |∫ t, (g (y - t) * FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.kernel m R t - g (z - t) * FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.kernel m R t) ∂m|
      ≤ ∫ t, (c : ℝ) * dist y z * FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.kernel m R t ∂m := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le hKint (ae_of_all _ fun t ↦ ?_)
        by_cases ht : FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.kernel m R t = 0
        · simp [ht]
        · rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.kernel_nonneg m R t)]
          refine mul_le_mul_of_nonneg_right ?_ (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.kernel_nonneg m R t)
          have htR : ‖t‖ < 2 * R := FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.norm_le_of_kernel_ne_zero m hR ht
          have hmem : ∀ w : V, ‖w - x‖ < δ → w - t ∈ Metric.ball x (δ + 2 * R) := by
            intro w hw
            rw [Metric.mem_ball, dist_eq_norm]
            have hrw : w - t - x = (w - x) - t := by abel
            have := norm_sub_le (w - x) t
            rw [hrw]
            linarith
          rw [← Real.dist_eq]
          calc dist (g (y - t)) (g (z - t)) ≤ (c : ℝ) * dist (y - t) (z - t) :=
                h.dist_le_mul _ (hmem y hyx) _ (hmem z hzx)
            _ = (c : ℝ) * dist y z := by rw [dist_sub_right]
    _ = (c : ℝ) * dist y z := by rw [integral_const_mul, FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.integral_kernel m hR, mul_one]
