-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.contDiff_covariance_pair_joint_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:17:57.993568+00:00
-- url     : https://prove2.me/submissions/a2245ca7-39b4-44a2-ad86-30efa8a18bd1

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_JointRegularity
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_posteriorExpectation_joint_readable

section
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
section
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

section
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
section
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
end
end
end

noncomputable section
open MeasureTheory ProbabilityTheory FunctionalInequalities
open scoped RealInnerProductSpace ContDiff
section Expectation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- A continuous statistic is bounded on the compact support, so its posterior expectation is jointly
`C^∞`. -/
theorem FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_joint_of_continuous (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {g : E → ℝ} (hg : Continuous g) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) => posteriorExpectation μ p.1 p.2 g) := by
  obtain ⟨C, _hC, hb⟩ := exists_bound_on_support_of_compact μ hc hg
  exact contDiff_posteriorExpectation_joint_readable μ hc hg.measurable hb
end Expectation
section Moments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- Covariances of two linear statistics under the posterior are jointly `C^∞` (polynomial moments of
the compact posterior). -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (u v : E) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) =>
      covariance (fun x => ⟪u, x⟫) (fun x => ⟪v, x⟫)
        ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent p.1 p.2))) := by
  have hs := FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_joint_of_continuous μ hc
    (g := fun x => ⟪u, x⟫ * ⟪v, x⟫) (by fun_prop)
  have hu := FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_joint_of_continuous μ hc (g := fun x => ⟪u, x⟫) (by fun_prop)
  have hv := FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_joint_of_continuous μ hc (g := fun x => ⟪v, x⟫) (by fun_prop)
  have he : (fun p : E × (E →L[ℝ] E) =>
      covariance (fun x => ⟪u, x⟫) (fun x => ⟪v, x⟫)
        ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent p.1 p.2))) =
      (fun p => FunctionalInequalities.Probability.Posterior.posteriorExpectation μ p.1 p.2 (fun x => ⟪u, x⟫ * ⟪v, x⟫)) -
        (fun p => FunctionalInequalities.Probability.Posterior.posteriorExpectation μ p.1 p.2 (fun x => ⟪u, x⟫)) *
        (fun p => FunctionalInequalities.Probability.Posterior.posteriorExpectation μ p.1 p.2 (fun x => ⟪v, x⟫)) := by
    funext p
    let : IsProbabilityMeasure ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent p.1 p.2)) :=
      FunctionalInequalities.Probability.Posterior.isProbabilityMeasure_tilted_quadraticExponent_of_compact μ hc p.1 p.2
    rw [covariance_eq_sub
      (FunctionalInequalities.Probability.Posterior.memLp_two_tilted_quadraticExponent_of_compact μ hc p.1 p.2
        (by fun_prop : Continuous (fun x => ⟪u, x⟫)))
      (FunctionalInequalities.Probability.Posterior.memLp_two_tilted_quadraticExponent_of_compact μ hc p.1 p.2
        (by fun_prop : Continuous (fun x => ⟪v, x⟫)))]
    rfl
  rw [he]
  exact hs.sub (hu.mul hv)
