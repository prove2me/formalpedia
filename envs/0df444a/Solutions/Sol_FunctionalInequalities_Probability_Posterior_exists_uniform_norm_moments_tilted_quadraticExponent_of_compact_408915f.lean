-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.exists_uniform_norm_moments_tilted_quadraticExponent_of_compact_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:57:26.916226+00:00
-- url     : https://prove2.me/submissions/f6bab028-25e7-49aa-8537-7584c05fbd95

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactQuadratic
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
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_norm_integral_tilted_le_of_compact_408915f

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
/-- Continuous statistics are in `L²` of every posterior of a compactly supported prior. -/
theorem FunctionalInequalities.Probability.Posterior.memLp_two_tilted_quadraticExponent_of_compact (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E)
    {f : E → ℝ} (hf : Continuous f) :
    MemLp f 2 ((μ : Measure E).tilted (quadraticExponent c Q)) := by
  obtain ⟨C, _hC, hb⟩ := exists_bound_on_support_of_compact μ hc hf
  have hφ : Continuous (quadraticExponent c Q) := by unfold quadraticExponent; fun_prop
  exact memLp_two_tilted_of_compact μ hc hφ hf.measurable hb
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities.Probability.Posterior in
/-- **Uniform posterior moments**: a support radius `R` bounds `∫ ‖x‖^p` under every posterior `(c, Q)`
by `R^p` (the bounded-moment input for (69)–(70); the stochastic equations themselves are not constructed). -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (c : E) (Q : E →L[ℝ] E) (p : ℕ),
      Integrable (fun x => ‖x‖ ^ p) ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q)) ∧
      (∫ x, ‖x‖ ^ p ∂((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q))) ≤ R ^ p := by
  obtain ⟨R, hR, hbound⟩ := FunctionalInequalities.Probability.Posterior.exists_bound_on_support_of_compact μ hc
    (continuous_norm : Continuous (fun x : E => ‖x‖))
  have hnorm : ∀ x ∈ (μ : Measure E).support, ‖x‖ ≤ R := by
    intro x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)] using hbound x hx
  refine ⟨R, hR, ?_⟩
  intro c Q p
  have hφ : Continuous (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q) := by unfold FunctionalInequalities.Probability.Posterior.quadraticExponent; fun_prop
  have hf : Continuous (fun x : E => ‖x‖ ^ p) := continuous_norm.pow p
  have hfb : ∀ x ∈ (μ : Measure E).support, ‖‖x‖ ^ p‖ ≤ R ^ p := by
    intro x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg x) p)]
    exact pow_le_pow_left₀ (norm_nonneg x) (hnorm x hx) p
  have hi2 := FunctionalInequalities.Probability.Posterior.memLp_two_tilted_quadraticExponent_of_compact μ hc c Q hf
  let : IsProbabilityMeasure ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q)) := FunctionalInequalities.Probability.Posterior.isProbabilityMeasure_tilted_quadraticExponent_of_compact μ hc c Q
  refine ⟨hi2.integrable one_le_two, ?_⟩
  have hle : (∫ x, ‖x‖ ^ p ∂((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q))) ≤
      ‖∫ x, ‖x‖ ^ p ∂((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q))‖ := le_abs_self _
  exact hle.trans (FunctionalInequalities.Probability.Posterior.norm_integral_tilted_le_of_compact_408915f μ hc
    hφ hf.measurable (pow_nonneg hR p) hfb)
