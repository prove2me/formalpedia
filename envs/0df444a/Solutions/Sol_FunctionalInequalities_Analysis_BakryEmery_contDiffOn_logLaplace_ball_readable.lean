-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.contDiffOn_logLaplace_ball_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:25:01.228323+00:00
-- url     : https://prove2.me/submissions/6cc42fdb-30cd-4a1e-9006-0efdc4feccfc

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section CumulantEstimates
omit [CompleteSpace E]
open scoped ContDiff in
/-- **Local smoothness of `Λ_μ`** (BKL p. 29, "finite and smooth in a neighborhood of the origin"):
one positive norm-exponential moment `∫ e^{r‖x‖} dμ < ∞` makes `Λ_μ` `C^∞` on the open ball of
radius `r`. The local integral identities are in `Tilt/Local.lean`. -/
theorem solution (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ] {r : ℝ}
    (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) :
    ContDiffOn ℝ ∞ (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ) (Metric.ball 0 r) := by
  have hgi : ∀ t < r,
      Integrable (fun x : E => Real.exp (t * ‖x‖) * ‖(1 : ℝ)‖) μ := by
    intro t ht
    refine hexp.mono' ?_ ?_
    · fun_prop
    · filter_upwards [] with x
      simp only [norm_one, mul_one, Real.norm_of_nonneg (Real.exp_pos _).le]
      by_cases ht0 : 0 ≤ t
      · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht.le (norm_nonneg x))
      · calc
          Real.exp (t * ‖x‖) ≤ 1 := Real.exp_le_one_iff.mpr
            (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ht0) (norm_nonneg x))
          _ ≤ Real.exp (r * ‖x‖) := Real.one_le_exp_iff.mpr
            (mul_nonneg hr.le (norm_nonneg x))
  have hZ : ContDiffOn ℝ ∞ (fun z : E => ∫ x, Real.exp ⟪z, x⟫ ∂μ)
      (Metric.ball 0 r) := by
    simpa only [smul_eq_mul, mul_one] using
      FunctionalInequalities.Analysis.BakryEmery.weighted_integral_contDiffOn μ measurable_const.aestronglyMeasurable hgi
  apply hZ.log
  intro z hz
  have hz' : ‖z‖ < r := by simpa using hz
  have hzint : Integrable (fun x : E => Real.exp ⟪z, x⟫) μ := by
    refine (hgi ‖z‖ hz').mono' ?_ ?_
    · exact (by fun_prop : Continuous (fun x : E => Real.exp ⟪z, x⟫)).aestronglyMeasurable
    · filter_upwards [] with x
      simp only [norm_one, mul_one, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (real_inner_le_norm z x)
  exact (integral_exp_pos hzint).ne'
