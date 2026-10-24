-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.hasDerivAt_weighted_integral_of_compact_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:03:42.780991+00:00
-- url     : https://prove2.me/submissions/a104009a-aafe-403a-95bb-f0286691b40a

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
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities.Probability.Posterior in
/-- Differentiation of the unnormalized tilted integral under a compact prior. -/
theorem solution (μ : ProbabilityMeasure Ω)
    (hc : IsCompact (μ : Measure Ω).support) {φ g f : Ω → ℝ}
    (hφ : Continuous φ) (hg : Continuous g) (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    HasDerivAt (fun t : ℝ => ∫ x, Real.exp (φ x + t * g x) * f x ∂(μ : Measure Ω))
      (∫ x, Real.exp (φ x) * g x * f x ∂(μ : Measure Ω)) 0 := by
  obtain ⟨P, _hP, hp⟩ := FunctionalInequalities.Probability.Posterior.exists_bound_on_support_of_compact μ hc hφ
  obtain ⟨G, hG, hgB⟩ := FunctionalInequalities.Probability.Posterior.exists_bound_on_support_of_compact μ hc hg
  let F : ℝ → Ω → ℝ := fun t x => Real.exp (φ x + t * g x) * f x
  let F' : ℝ → Ω → ℝ := fun t x => Real.exp (φ x + t * g x) * g x * f x
  have he (t : ℝ) : Continuous (fun x => Real.exp (φ x + t * g x)) :=
    Real.continuous_exp.comp (hφ.add (hg.const_mul t))
  have hmeas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) (μ : Measure Ω) :=
    Eventually.of_forall fun t => (he t).aestronglyMeasurable.mul hf.aestronglyMeasurable
  have hi : Integrable (F 0) (μ : Measure Ω) := by
    simpa only [F, zero_mul, add_zero] using FunctionalInequalities.Probability.Posterior.integrable_exp_mul_of_compact μ hc hφ hf hC hfb
  have hm' : AEStronglyMeasurable (F' 0) (μ : Measure Ω) :=
    ((he 0).aestronglyMeasurable.mul hg.aestronglyMeasurable).mul hf.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(μ : Measure Ω), ∀ t ∈ Metric.ball (0 : ℝ) 1,
      ‖F' t x‖ ≤ Real.exp (P + G) * G * C := by
    filter_upwards [(μ : Measure Ω).support_mem_ae] with x hx t ht
    have ht' : |t| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
    have htg : t * g x ≤ G := by
      calc
        t * g x ≤ |t * g x| := le_abs_self _
        _ = |t| * |g x| := abs_mul _ _
        _ ≤ |t| * G := mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hgB x hx) (abs_nonneg _)
        _ ≤ G := by nlinarith
    have hφx : φ x ≤ P := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hp x hx)
    have hex : Real.exp (φ x + t * g x) ≤ Real.exp (P + G) := Real.exp_le_exp.mpr (by linarith)
    change |Real.exp (φ x + t * g x) * g x * f x| ≤ Real.exp (P + G) * G * C
    simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul ?_ (by simpa only [Real.norm_eq_abs] using hfb x hx)
      (abs_nonneg _) (mul_nonneg (Real.exp_nonneg _) hG)
    exact mul_le_mul hex (by simpa only [Real.norm_eq_abs] using hgB x hx)
      (abs_nonneg _) (Real.exp_nonneg _)
  have hdiff : ∀ᵐ x ∂(μ : Measure Ω), ∀ t ∈ Metric.ball (0 : ℝ) 1, HasDerivAt (F · x) (F' t x) t := by
    filter_upwards [] with x t _ht
    convert! ((((hasDerivAt_id t).mul_const (g x)).const_add (φ x)).exp.mul_const (f x)) using 1
    simp only [F', one_mul, id_eq]
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)) hmeas hi hm' hbound
    (integrable_const (Real.exp (P + G) * G * C)) hdiff
  simpa only [F, F', zero_mul, add_zero] using hd.2
