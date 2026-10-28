-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.tendsto_iteratedFDeriv_laplace_cond_closedBall_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:27:25.011048+00:00
-- url     : https://prove2.me/submissions/98943aab-8d92-49d9-8e43-8972d27a106c

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Truncation
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_norm_iteratedFDeriv_laplace_cond_sub_le_readable

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
section CondHelpers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Norm moments of every order from one positive exponential moment. -/
theorem FunctionalInequalities.Analysis.BakryEmery.integrable_norm_pow_of_exp_cond (μ : Measure E) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (d : ℕ) :
    Integrable (fun x : E => ‖x‖ ^ d) μ := by
  have hneg : Integrable (fun x : E => Real.exp (-r * ‖x‖)) μ := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hr.le) (norm_nonneg x))
  simpa only [abs_norm] using
    ProbabilityTheory.integrable_pow_abs_of_integrable_exp_mul hr.ne' hexp hneg d
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
theorem FunctionalInequalities.Analysis.BakryEmery.eventually_measure_closedBall_ne_zero_cond (ν : Measure E) [IsProbabilityMeasure ν] :
    ∀ᶠ R : ℕ in atTop, ν (Metric.closedBall (0 : E) R) ≠ 0 := by
  have hmono : Monotone fun R : ℕ => Metric.closedBall (0 : E) (R : ℝ) := fun m n hmn =>
    Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
  have hB : Tendsto (fun R : ℕ => ν (Metric.closedBall (0 : E) R)) atTop (𝓝 1) := by
    have := tendsto_measure_iUnion_atTop (μ := ν) hmono
    rwa [Metric.iUnion_closedBall_nat, measure_univ] at this
  filter_upwards [hB.eventually (lt_mem_nhds (zero_lt_one' ENNReal))] with R hR
  exact hR.ne'
/-- Moment tensors of the ball truncations converge in operator norm. -/
theorem solution (ν : Measure E) [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) ν) (d : ℕ) :
    Tendsto (fun R : ℕ => iteratedFDeriv ℝ d
        (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂(ν[|Metric.closedBall (0 : E) R])) 0) atTop
      (𝓝 (iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂ν) 0)) := by
  have hpow := FunctionalInequalities.Analysis.BakryEmery.integrable_norm_pow_of_exp_cond ν hr hexp d
  have hmono : Monotone fun R : ℕ => Metric.closedBall (0 : E) (R : ℝ) := fun m n hmn =>
    Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
  have hmeas : ∀ R : ℕ, MeasurableSet (Metric.closedBall (0 : E) (R : ℝ)) := fun R =>
    Metric.isClosed_closedBall.measurableSet
  have hB : Tendsto (fun R : ℕ => ν (Metric.closedBall (0 : E) R)) atTop (𝓝 1) := by
    have := tendsto_measure_iUnion_atTop (μ := ν) hmono
    rwa [Metric.iUnion_closedBall_nat, measure_univ] at this
  have hc : Tendsto (fun R : ℕ => ((ν (Metric.closedBall (0 : E) R))⁻¹).toReal) atTop (𝓝 1) := by
    have h1 : Tendsto (fun R : ℕ => (ν (Metric.closedBall (0 : E) R)).toReal) atTop (𝓝 1) := by
      have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hB
      simpa [Function.comp_def] using this
    have := h1.inv₀ one_ne_zero
    simpa [ENNReal.toReal_inv] using this
  have hm : Tendsto (fun R : ℕ => ∫ x in Metric.closedBall (0 : E) R, ‖x‖ ^ d ∂ν) atTop
      (𝓝 (∫ x, ‖x‖ ^ d ∂ν)) := by
    have := tendsto_setIntegral_of_monotone hmeas hmono hpow.integrableOn
    rwa [Metric.iUnion_closedBall_nat, Measure.restrict_univ] at this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun R : ℕ =>
      |((ν (Metric.closedBall (0 : E) R))⁻¹).toReal - 1| * ∫ x, ‖x‖ ^ d ∂ν +
        ((∫ x, ‖x‖ ^ d ∂ν) - ∫ x in Metric.closedBall (0 : E) R, ‖x‖ ^ d ∂ν))
    (Eventually.of_forall fun R => norm_nonneg _) ?_ ?_
  · filter_upwards [FunctionalInequalities.Analysis.BakryEmery.eventually_measure_closedBall_ne_zero_cond ν] with R hR
    have h1 := FunctionalInequalities.Analysis.BakryEmery.norm_iteratedFDeriv_laplace_cond_sub_le_readable ν hr hexp d (hmeas R) hR
    have h2 := integral_add_compl (hmeas R) hpow
    calc
      _ ≤ _ := h1
      _ = |((ν (Metric.closedBall (0 : E) R))⁻¹).toReal - 1| * ∫ x, ‖x‖ ^ d ∂ν +
          ((∫ x, ‖x‖ ^ d ∂ν) - ∫ x in Metric.closedBall (0 : E) R, ‖x‖ ^ d ∂ν) := by
        rw [← h2]; ring
  · have := ((hc.sub_const 1).abs.mul_const (∫ x, ‖x‖ ^ d ∂ν)).add ((tendsto_const_nhds (x := ∫ x, ‖x‖ ^ d ∂ν)).sub hm)
    simpa using this
