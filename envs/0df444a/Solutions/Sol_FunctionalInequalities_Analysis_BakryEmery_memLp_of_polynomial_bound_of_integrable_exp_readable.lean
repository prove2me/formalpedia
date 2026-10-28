-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.memLp_of_polynomial_bound_of_integrable_exp_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:25:23.073461+00:00
-- url     : https://prove2.me/submissions/b028af77-d8ee-4c34-a623-0bbaa268cb28

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem FunctionalInequalities.Analysis.BakryEmery.norm_pow_integrable (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (k : ℕ) :
    Integrable (fun x => ‖x‖ ^ k) μ := by
  have hneg : Integrable (fun x => Real.exp (-r * ‖x‖)) μ := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr.le) (norm_nonneg _))
  have h := ProbabilityTheory.integrable_pow_abs_of_integrable_exp_mul hr.ne' hexp hneg k
  simpa only [abs_norm] using h
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A continuous function with a polynomial bound is in `L²(μ)` when `μ` has one exponential moment. -/
theorem solution (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {g : E → ℝ} (hg : Continuous g) {C : ℝ} {k : ℕ}
    (hb : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖) ^ k) : MemLp g 2 μ := by
  apply (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2
  have hi := ((integrable_const (1 : ℝ)).add (FunctionalInequalities.Analysis.BakryEmery.norm_pow_integrable μ hr hexp (k * 2))).const_mul
    (C ^ 2 * 2 ^ (k * 2 - 1))
  refine hi.mono' (hg.pow 2).aestronglyMeasurable ?_
  filter_upwards [] with x
  calc
    ‖g x ^ 2‖ = ‖g x‖ ^ 2 := norm_pow _ _
    _ ≤ (C * (1 + ‖x‖) ^ k) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hb x) 2
    _ = C ^ 2 * (1 + ‖x‖) ^ (k * 2) := by rw [mul_pow, ← pow_mul]
    _ ≤ C ^ 2 * (2 ^ (k * 2 - 1) * (1 + ‖x‖ ^ (k * 2))) := by
      gcongr
      simpa only [one_pow] using add_pow_le (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg x) (k * 2)
    _ = (C ^ 2 * 2 ^ (k * 2 - 1)) * (1 + ‖x‖ ^ (k * 2)) := by ring
