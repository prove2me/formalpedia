-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_norm_sq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:22:15.678445+00:00
-- url     : https://prove2.me/submissions/87de7072-d5b3-4cd9-9857-83d48e4c031a

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_exp_norm_integrable_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_smoothedLaw_inner_sq_readable

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
omit [CompleteSpace E] in
/-- The smoothed law `μ * γ_s` has a finite second moment when `μ` does. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_memLp_two (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) : MemLp id 2 (smoothedLaw μ s) := by
  let _ : IsProbabilityMeasure (gaussianLaw (V := E) s) := gaussianLaw_probability hs
  unfold smoothedLaw Measure.conv
  apply (memLp_map_measure_iff continuous_id.aestronglyMeasurable
    (by fun_prop : AEMeasurable (fun p : E × E => p.1 + p.2) _)).2
  exact (hμ2.comp_fst (gaussianLaw s)).add ((gaussianLaw_memLp_two hs).comp_snd μ)
/-- `∫ ‖y‖² d(μ*γ_s) = ∫ ‖y‖² dμ + n/(2s)`. -/
theorem solution (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) :
    (∫ y : E, ‖y‖ ^ 2 ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw μ s)) =
      (∫ y : E, ‖y‖ ^ 2 ∂μ) + (Module.finrank ℝ E : ℝ) / (2 * s) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have hsm2 := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_memLp_two μ hμ2 hs
  have hi (ν : Measure E) (hν : MemLp id 2 ν) (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun y : E => ⟪b i, y⟫ ^ 2) ν := by
    have h : MemLp (fun y : E => ⟪b i, y⟫) 2 ν := by
      simpa only [id_eq, innerSL_apply_apply] using hν.continuousLinearMap_comp (innerSL ℝ (b i))
    exact (memLp_two_iff_integrable_sq h.aestronglyMeasurable).1 h
  have heq : (fun y : E => ‖y‖ ^ 2) = fun y => ∑ i, ⟪b i, y⟫ ^ 2 := by
    funext y
    exact (b.sum_sq_inner_right y).symm
  rw [heq, integral_finsetSum Finset.univ (fun i _ => hi _ hsm2 i),
    integral_finsetSum Finset.univ (fun i _ => hi _ hμ2 i)]
  simp_rw [FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_inner_sq_readable μ hμ2 hs]
  rw [Finset.sum_add_distrib]
  congr 1
  simp only [b.norm_eq_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring
