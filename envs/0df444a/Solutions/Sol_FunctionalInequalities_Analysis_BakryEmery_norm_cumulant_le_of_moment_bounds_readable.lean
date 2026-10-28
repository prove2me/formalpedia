-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.norm_cumulant_le_of_moment_bounds_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:26:10.159533+00:00
-- url     : https://prove2.me/submissions/4ad0c214-6e3c-421f-82e4-002c076c3ec9

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_MomentBound

section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
theorem FunctionalInequalities.Analysis.BakryEmery.norm_exp_weights {μ : Measure E} {r : ℝ}
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) :
    ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖(1 : ℝ)‖) μ := by
  intro t ht
  simp only [norm_one, mul_one]
  refine hexp.mono' (by fun_prop) ?_
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht.le (norm_nonneg _))
end
end

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Analysis
/-- Cumulants are bounded by moments. -/
theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] {r : ℝ} (hr : 0 < r)
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) ν) {m : ℕ} {D : ℝ}
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ m → (∫ x, ‖x‖ ^ i ∂ν) ≤ D ^ i) :
    ‖FunctionalInequalities.Analysis.BakryEmery.cumulant ν m‖ ≤ (m.factorial : ℝ) ^ 2 * D ^ m := by
  have hf : ContDiffOn ℝ ∞ (fun z : E => ∫ x, Real.exp ⟪z, x⟫ ∂ν)
      (Metric.ball 0 r) := by
    simpa only [smul_eq_mul, mul_one] using
      FunctionalInequalities.Analysis.BakryEmery.weighted_integral_contDiffOn ν
        (g := fun _ : E => (1 : ℝ))
        measurable_const.aestronglyMeasurable (FunctionalInequalities.Analysis.BakryEmery.norm_exp_weights hexp)
  have hpos : ∀ z ∈ Metric.ball (0 : E) r, 0 < ∫ x, Real.exp ⟪z, x⟫ ∂ν := by
    intro z hz
    apply integral_exp_pos
    have hz' : ‖z‖ < r := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    simpa only [smul_eq_mul, mul_one] using
      FunctionalInequalities.Analysis.BakryEmery.integrable_exp_inner_smul_of_lt ν
        (g := fun _ : E => (1 : ℝ))
        measurable_const.aestronglyMeasurable (FunctionalInequalities.Analysis.BakryEmery.norm_exp_weights hexp) hz'
  have hone : (∫ x : E, Real.exp ⟪(0 : E), x⟫ ∂ν) = 1 := by simp
  exact FunctionalInequalities.Analysis.norm_iteratedFDeriv_log_comp_le_factorial_sq Metric.isOpen_ball
    (by simpa only [Metric.mem_ball, dist_self] using hr) hf hpos hone
    (fun i hi him =>
      (FunctionalInequalities.Analysis.BakryEmery.norm_iteratedFDeriv_laplace_zero_le ν hr hexp i).trans (hD i hi him))
