-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_exp_norm_integrable_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:35:13.787994+00:00
-- url     : https://prove2.me/submissions/889fd648-c764-4778-a089-a6ef77ef619a

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments

section
open MeasureTheory ProbabilityTheory Filter Topology
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] in
/-- The Gaussian noise law `γ_s` is the tilt of Lebesgue measure by `e^{-s‖y‖²}`. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_eq_tilted {s : ℝ} (hs : 0 < s) :
    gaussianLaw (V := E) s = (volume : Measure E).tilted (fun y => -s * ‖y‖ ^ 2) := by
  have hmass : (∫ y : E, Real.exp (-s * ‖y‖ ^ 2)) = mass (V := E) s := integral_kernel hs
  unfold gaussianLaw Measure.tilted normalizedKernel kernel
  rw [hmass]
omit [CompleteSpace E] in
/-- `∫ e^{‖y‖} dγ_s < ∞`. -/
theorem solution {s : ℝ} (hs : 0 < s) :
    Integrable (fun y : E => Real.exp ‖y‖) (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s) := by
  rw [FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_eq_tilted hs]
  have hk : Integrable (fun y : E => Real.exp (-s * ‖y‖ ^ 2)) volume := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integrable_kernel hs
  rw [integrable_tilted_iff hk]
  have hh : Integrable (fun y : E => Real.exp (-(s / 2) * ‖y‖ ^ 2)) volume :=
    FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integrable_kernel (by positivity : 0 < s / 2)
  refine (hh.const_mul (Real.exp (1 / (2 * s)))).mono' (by fun_prop) ?_
  filter_upwards [] with y
  rw [smul_eq_mul, Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le),
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hquad : ‖y‖ - s / 2 * ‖y‖ ^ 2 ≤ 1 / (2 * s) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hs)).2
    nlinarith [sq_nonneg (s * ‖y‖ - 1)]
  nlinarith
