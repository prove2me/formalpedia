-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.logLaplace_compactPosterior_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:28:22.535908+00:00
-- url     : https://prove2.me/submissions/b77a955f-1835-41de-9702-043a13ee21f8

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Exponent
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_LogPartition

section
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- A tilted expectation as the ratio of prior integrals. -/
theorem FunctionalInequalities.Probability.Posterior.integral_tilted_eq_div {Ω : Type*} [MeasurableSpace Ω] (μ : ProbabilityMeasure Ω)
    (φ f : Ω → ℝ) :
    (∫ x, f x ∂((μ : Measure Ω).tilted φ)) =
      (∫ x, Real.exp (φ x) * f x ∂(μ : Measure Ω)) / ∫ x, Real.exp (φ x) ∂(μ : Measure Ω) := by
  rw [integral_tilted]
  simp only [smul_eq_mul, div_mul_eq_mul_div]
  exact integral_div _ _
end
end
end

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
theorem solution
    [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) (z : E) :
    FunctionalInequalities.Analysis.BakryEmery.logLaplace (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc c Q : Measure E) z =
      FunctionalInequalities.Probability.Posterior.logPartition μ (c + z) Q - FunctionalInequalities.Probability.Posterior.logPartition μ c Q := by
  unfold FunctionalInequalities.Analysis.BakryEmery.logLaplace
  change Real.log
      (∫ x, Real.exp ⟪z, x⟫
        ∂((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q))) =
      FunctionalInequalities.Probability.Posterior.logPartition μ (c + z) Q - FunctionalInequalities.Probability.Posterior.logPartition μ c Q
  rw [FunctionalInequalities.Probability.Posterior.integral_tilted_eq_div]
  have heq :
      (fun x : E =>
        Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x) * Real.exp ⟪z, x⟫) =
      (fun x : E => Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent (c + z) Q x)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    simp only [FunctionalInequalities.Probability.Posterior.quadraticExponent, inner_add_left]
    ring
  rw [heq]
  simp only [FunctionalInequalities.Probability.Posterior.logPartition]
  rw [Real.log_div
    (integral_exp_pos
      (FunctionalInequalities.Probability.Posterior.integrable_exp_of_compact μ hc (by
        unfold FunctionalInequalities.Probability.Posterior.quadraticExponent
        fun_prop))).ne'
    (integral_exp_pos
      (FunctionalInequalities.Probability.Posterior.integrable_exp_of_compact μ hc (by
        unfold FunctionalInequalities.Probability.Posterior.quadraticExponent
        fun_prop))).ne']
