-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.integrable_exp_mul_norm_of_memLp_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:25:02.93412+00:00
-- url     : https://prove2.me/submissions/061c044f-d765-4498-b727-0e923025d771

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section IntegralCalculus
omit [CompleteSpace E]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Square-integrable functions are integrable against every exponential weight when `μ` is
finite with all exponential moments. -/
theorem solution (μ : Measure E) [IsFiniteMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f : E → ℝ} (hf : MemLp f 2 μ)
    (r : ℝ) : Integrable (fun x => Real.exp (r * ‖x‖) * ‖f x‖) μ := by
    have hmeas : AEStronglyMeasurable (fun x : E => Real.exp (r * ‖x‖)) μ :=
      (Real.continuous_exp.comp
        (continuous_const.mul (continuous_norm : Continuous (fun x : E => ‖x‖)))).aestronglyMeasurable
    have hsquare :
        Integrable (fun x => (Real.exp (r * ‖x‖)) ^ (2 : ℕ)) μ := by
      convert hexp (2 * r) using 1
      funext x
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hg : MemLp (fun x : E => Real.exp (r * ‖x‖)) 2 μ :=
      (memLp_two_iff_integrable_sq hmeas).2 hsquare
    have hprod :
        Integrable
          ((fun x : E => Real.exp (r * ‖x‖)) * (fun x : E => ‖f x‖)) μ :=
      hg.integrable_mul hf.norm
    have heq :
        (fun x : E => Real.exp (r * ‖x‖)) * (fun x : E => ‖f x‖) =
          (fun x : E => Real.exp (r * ‖x‖) * ‖f x‖) := by
      funext x
      rfl
    exact heq ▸ hprod
