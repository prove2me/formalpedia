-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.cumulant_eq_taylorComp_cond_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:25:05.396255+00:00
-- url     : https://prove2.me/submissions/d0bc08ac-c83a-4c10-b671-8007bf89f976

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Truncation

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
section CondHelpers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The cumulant tensor as the Faà di Bruno composition of the Taylor jets of `log` at `1` and of
the Laplace transform at `0`. -/
theorem solution (μ : Measure E) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (k : ℕ) :
    FunctionalInequalities.Analysis.BakryEmery.cumulant μ k = (ftaylorSeriesWithin ℝ Real.log {0}ᶜ 1).taylorComp
      (ftaylorSeriesWithin ℝ (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂μ) (Metric.ball 0 r) 0) k := by
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
  have hpos : ∀ z ∈ Metric.ball (0 : E) r, 0 < ∫ x, Real.exp ⟪z, x⟫ ∂μ := by
    intro z hz
    have hz' : ‖z‖ < r := by simpa using hz
    have hzint : Integrable (fun x : E => Real.exp ⟪z, x⟫) μ := by
      refine (hgi ‖z‖ hz').mono' ?_ ?_
      · exact (by fun_prop : Continuous (fun x : E => Real.exp ⟪z, x⟫)).aestronglyMeasurable
      · filter_upwards [] with x
        simp only [norm_one, mul_one, Real.norm_of_nonneg (Real.exp_pos _).le]
        exact Real.exp_le_exp.mpr (real_inner_le_norm z x)
    exact integral_exp_pos hzint
  have hU : UniqueDiffOn ℝ (Metric.ball (0 : E) r) := Metric.isOpen_ball.uniqueDiffOn
  have hf : HasFTaylorSeriesUpToOn k (fun z : E => ∫ x, Real.exp ⟪z, x⟫ ∂μ)
      (ftaylorSeriesWithin ℝ (fun z : E => ∫ x, Real.exp ⟪z, x⟫ ∂μ) (Metric.ball 0 r))
      (Metric.ball 0 r) :=
    (hZ.of_le (WithTop.coe_le_coe.mpr le_top)).ftaylorSeriesWithin hU
  have hg : HasFTaylorSeriesUpToOn k Real.log (ftaylorSeriesWithin ℝ Real.log {0}ᶜ) {0}ᶜ :=
    (Real.contDiffOn_log (n := k)).ftaylorSeriesWithin isOpen_compl_singleton.uniqueDiffOn
  have hmaps : Set.MapsTo (fun z : E => ∫ x, Real.exp ⟪z, x⟫ ∂μ) (Metric.ball 0 r) {0}ᶜ :=
    fun z hz => (hpos z hz).ne'
  have hcomp := hg.comp hf hmaps
  have h0 : (0 : E) ∈ Metric.ball (0 : E) r := Metric.mem_ball_self hr
  have heq := hcomp.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hU h0
  have hZ0 : (∫ x, Real.exp ⟪(0 : E), x⟫ ∂μ) = 1 := by simp
  rw [hZ0] at heq
  have hlog : FunctionalInequalities.Analysis.BakryEmery.logLaplace μ = Real.log ∘ (fun z : E => ∫ x, Real.exp ⟪z, x⟫ ∂μ) := rfl
  unfold FunctionalInequalities.Analysis.BakryEmery.cumulant
  rw [hlog, ← iteratedFDerivWithin_of_isOpen k Metric.isOpen_ball h0, ← heq]
