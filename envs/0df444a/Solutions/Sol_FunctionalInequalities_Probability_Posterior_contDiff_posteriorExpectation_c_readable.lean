-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_c_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:05:41.471488+00:00
-- url     : https://prove2.me/submissions/b4d0633a-2e15-4a61-9a12-21afa79b1e35

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Exponent
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Generator
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_weighted_integral_quadraticExponent_of_compact_readable

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
open MeasureTheory Filter Topology ProbabilityTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section Smooth
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The posterior expectation is `C^∞` in `c` at every fixed `Q`, including `Q = 0`. -/
theorem solution (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) (Q : E →L[ℝ] E) :
    ContDiff ℝ ∞ (fun c => FunctionalInequalities.Probability.Posterior.posteriorExpectation μ c Q f) := by
  have hN := FunctionalInequalities.Probability.Posterior.contDiff_weighted_integral_quadraticExponent_of_compact_readable μ hc hf hC hfb Q
  have hZ := FunctionalInequalities.Probability.Posterior.contDiff_weighted_integral_quadraticExponent_of_compact_readable μ hc (f := fun _ => (1 : ℝ)) measurable_const
    (C := 1) (by norm_num) (by intro x hx; simp) Q
  simp only [mul_one] at hZ
  have hpos (c : E) : (∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x) ∂(μ : Measure E)) ≠ 0 := by
    apply (integral_exp_pos (FunctionalInequalities.Probability.Posterior.integrable_exp_of_compact μ hc ?_)).ne'
    unfold FunctionalInequalities.Probability.Posterior.quadraticExponent
    fun_prop
  have heq : (fun c => FunctionalInequalities.Probability.Posterior.posteriorExpectation μ c Q f) =
      fun c => (∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x) * f x ∂(μ : Measure E)) /
        ∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x) ∂(μ : Measure E) := by
    funext c
    exact FunctionalInequalities.Probability.Posterior.integral_tilted_eq_div μ _ _
  rw [heq]
  exact hN.div hZ hpos
