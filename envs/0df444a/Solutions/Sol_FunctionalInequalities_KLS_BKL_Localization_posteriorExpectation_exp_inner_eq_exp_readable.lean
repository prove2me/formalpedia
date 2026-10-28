-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.posteriorExpectation_exp_inner_eq_exp_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:33:49.452147+00:00
-- url     : https://prove2.me/submissions/39f3ba0e-97a3-4aab-8444-aa989bdc0396

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Exponent
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_LogLaplaceGenerator

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
open MeasureTheory
open scoped RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion
open scoped ContDiff
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
include hc in
/-- The posterior expectation of `e^{⟪z,·⟫}` is `exp (ψ(c + z, Q) − ψ(c, Q))`. -/
theorem solution (z : EuclideanSpace ℝ (Fin n)) (q : FunctionalInequalities.KLS.BKL.Localization.Param n) :
    FunctionalInequalities.Probability.Posterior.posteriorExpectation μ q.1 q.2 (fun x => Real.exp ⟪z, x⟫) =
      Real.exp (FunctionalInequalities.Probability.Posterior.logPartition μ (q.1 + z) q.2 - FunctionalInequalities.Probability.Posterior.logPartition μ q.1 q.2) := by
  have hpos : ∀ (c : EuclideanSpace ℝ (Fin n)) (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
      0 < ∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x) ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) :=
    fun c Q => integral_exp_pos (FunctionalInequalities.Probability.Posterior.integrable_exp_of_compact μ hc (by
      unfold FunctionalInequalities.Probability.Posterior.quadraticExponent
      fun_prop))
  have heq : (fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent q.1 q.2 x) * Real.exp ⟪z, x⟫) =
      fun x => Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent (q.1 + z) q.2 x) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    simp only [FunctionalInequalities.Probability.Posterior.quadraticExponent, inner_add_left]
    ring
  unfold FunctionalInequalities.Probability.Posterior.posteriorExpectation FunctionalInequalities.Probability.Posterior.logPartition
  rw [FunctionalInequalities.Probability.Posterior.integral_tilted_eq_div, heq, Real.exp_sub, Real.exp_log (hpos _ _), Real.exp_log (hpos _ _)]
