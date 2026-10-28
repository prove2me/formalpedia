-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_mean_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:39:52.284982+00:00
-- url     : https://prove2.me/submissions/0a383d08-d51e-4def-94ca-b9c31db791da

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_exp_norm_integrable_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_mean_zero_readable

section
open MeasureTheory ProbabilityTheory Filter Topology
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] in
/-- `γ_s` has a finite second moment. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_memLp_two {s : ℝ} (hs : 0 < s) : MemLp id 2 (gaussianLaw (V := E) s) := by
  let _ : IsProbabilityMeasure (gaussianLaw (V := E) s) := gaussianLaw_probability hs
  have he : Integrable (fun y : E => Real.exp ((1 : ℝ) * ‖y‖)) (gaussianLaw s) := by
    simpa only [one_mul] using gaussianLaw_exp_norm_integrable_readable (E := E) hs
  exact (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
    (Probability.integrable_norm_pow_of_integrable_exp_norm (by norm_num : (0 : ℝ) < 1) he 2)
/-- Gaussian smoothing preserves the mean. -/
theorem solution (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) :
    (∫ y : E, y ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw μ s)) = ∫ y : E, y ∂μ := by
  let _ : IsProbabilityMeasure (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw (V := E) s) := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_probability hs
  have hfirst : Integrable (fun p : E × E => p.1) (μ.prod (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s)) :=
    (hμ2.comp_fst (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s)).integrable one_le_two
  have hsecond : Integrable (fun p : E × E => p.2) (μ.prod (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s)) :=
    ((FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_memLp_two hs).comp_snd μ).integrable one_le_two
  unfold FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw Measure.conv
  change (∫ y, id y ∂(Measure.map (fun p : E × E => p.1 + p.2) (μ.prod (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s)))) = _
  rw [integral_map (by fun_prop) continuous_id.aestronglyMeasurable]
  change (∫ p : E × E, p.1 + p.2 ∂(μ.prod (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s))) = _
  rw [integral_add hfirst hsecond, integral_fun_fst (fun y : E => y), integral_fun_snd (fun y : E => y),
    FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_mean_zero_readable hs]
  simp
