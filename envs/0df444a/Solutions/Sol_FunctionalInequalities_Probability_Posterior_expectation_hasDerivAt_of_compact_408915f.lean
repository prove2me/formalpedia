-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.expectation_hasDerivAt_of_compact_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:04:30.767328+00:00
-- url     : https://prove2.me/submissions/89668445-ae23-48ec-b795-8b5f9853c7ab

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Exponent
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Covariance
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_hasDerivAt_weighted_integral_of_compact_408915f

section
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Posterior
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
end
end

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Posterior
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [SecondCountableTopology Ω]
/-- A measurable statistic bounded on the support is in `L²` of the tilt. -/
theorem FunctionalInequalities.Probability.Posterior.memLp_two_tilted_of_compact (μ : ProbabilityMeasure Ω) (hc : IsCompact (μ : Measure Ω).support)
    {φ f : Ω → ℝ} (hφ : Continuous φ) (hf : Measurable f) {C : ℝ}
    (hb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    MemLp f 2 ((μ : Measure Ω).tilted φ) := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
  apply (integrable_tilted_iff (integrable_exp_of_compact μ hc hφ) (fun x => f x ^ 2)).mpr
  have hd : Integrable (fun x => Real.exp (φ x) * f x ^ 2) (μ : Measure Ω) := by
    apply integrable_exp_mul_of_compact μ hc hφ (hf.pow_const 2) (C := C ^ 2) (sq_nonneg C)
    intro x hx
    rw [norm_pow]
    have hB : 0 ≤ C := (norm_nonneg (f x)).trans (hb x hx)
    exact (sq_le_sq₀ (norm_nonneg _) hB).mpr (hb x hx)
  simpa only [smul_eq_mul] using hd
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities.Probability.Posterior in
/-- **First variation of a tilted expectation under a compact prior**: for continuous `φ, g` and a
measurable `f` bounded on the support, `t ↦ ∫ f d(μ.tilted (φ + t g))` has derivative
`Cov_{μ.tilted φ}(f, g)` at `t = 0`. Zero parameters are allowed. -/
theorem solution (μ : ProbabilityMeasure Ω)
    (hc : IsCompact (μ : Measure Ω).support) {φ g f : Ω → ℝ}
    (hφ : Continuous φ) (hg : Continuous g) (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    HasDerivAt (fun t : ℝ => ∫ x, f x ∂((μ : Measure Ω).tilted (fun x => φ x + t * g x)))
      (covariance f g ((μ : Measure Ω).tilted φ)) 0 := by
  have hN := FunctionalInequalities.Probability.Posterior.hasDerivAt_weighted_integral_of_compact_408915f μ hc hφ hg hf hC hfb
  have hZ := FunctionalInequalities.Probability.Posterior.hasDerivAt_weighted_integral_of_compact_408915f μ hc hφ hg
    (f := fun _ => (1 : ℝ)) measurable_const (C := 1) (by norm_num) (by intro x hx; simp)
  simp only [mul_one] at hZ
  have hZi := FunctionalInequalities.Probability.Posterior.integrable_exp_of_compact μ hc hφ
  have hZne : (∫ x, Real.exp (φ x) ∂(μ : Measure Ω)) ≠ 0 := (integral_exp_pos hZi).ne'
  let : IsProbabilityMeasure ((μ : Measure Ω).tilted φ) :=
    FunctionalInequalities.Probability.Posterior.isProbabilityMeasure_tilted_of_compact μ hc hφ
  have hF2 := FunctionalInequalities.Probability.Posterior.memLp_two_tilted_of_compact μ hc hφ hf hfb
  obtain ⟨G, _hG, hgb⟩ := FunctionalInequalities.Probability.Posterior.exists_bound_on_support_of_compact μ hc hg
  have hG2 := FunctionalInequalities.Probability.Posterior.memLp_two_tilted_of_compact μ hc hφ hg.measurable hgb
  have hcov : covariance f g ((μ : Measure Ω).tilted φ) =
      ((∫ x, Real.exp (φ x) * g x * f x ∂(μ : Measure Ω)) *
        (∫ x, Real.exp (φ x) ∂(μ : Measure Ω)) -
        (∫ x, Real.exp (φ x) * f x ∂(μ : Measure Ω)) *
        (∫ x, Real.exp (φ x) * g x ∂(μ : Measure Ω))) /
        (∫ x, Real.exp (φ x) ∂(μ : Measure Ω)) ^ 2 := by
    rw [covariance_eq_sub hF2 hG2, FunctionalInequalities.Probability.Posterior.integral_tilted_eq_div, FunctionalInequalities.Probability.Posterior.integral_tilted_eq_div, FunctionalInequalities.Probability.Posterior.integral_tilted_eq_div]
    simp only [Pi.mul_apply]
    have heq : (fun x => Real.exp (φ x) * (f x * g x)) =
        fun x => Real.exp (φ x) * g x * f x := by funext x; ring
    rw [heq]
    field_simp
  have hd := hN.div hZ (by simpa only [zero_mul, add_zero] using hZne)
  have hfunc : (fun t : ℝ => ∫ x, f x ∂((μ : Measure Ω).tilted (fun x => φ x + t * g x))) =
      fun t => (∫ x, Real.exp (φ x + t * g x) * f x ∂(μ : Measure Ω)) /
        ∫ x, Real.exp (φ x + t * g x) ∂(μ : Measure Ω) := by
    funext t
    exact FunctionalInequalities.Probability.Posterior.integral_tilted_eq_div μ _ _
  rw [hfunc, hcov]
  convert! hd using 1
  simp only [zero_mul, add_zero]
