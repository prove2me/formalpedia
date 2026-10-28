-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.contDiff_posteriorMean_joint_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:17:59.170995+00:00
-- url     : https://prove2.me/submissions/89fdb8ee-f984-4806-a5c8-c6d86f3d3bc2

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Generator
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_JointRegularity
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_posteriorExpectation_joint_readable
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_exists_uniform_norm_moments_tilted_quadraticExponent_of_compact_readable

section
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section Mean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- `∫ ⟪h, x⟫ dμ_{c,Q} = ⟪h, a⟫` (finite second moment from compact support). -/
theorem FunctionalInequalities.Probability.Posterior.integral_inner_eq_inner_posteriorMean (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) (h : E) :
    (∫ x, ⟪h, x⟫ ∂((μ : Measure E).tilted (quadraticExponent c Q))) = ⟪h, posteriorMean μ c Q⟫ := by
  obtain ⟨R, _hR, hmom⟩ := exists_uniform_norm_moments_tilted_quadraticExponent_of_compact_readable μ hc
  let : IsProbabilityMeasure ((μ : Measure E).tilted (quadraticExponent c Q)) := isProbabilityMeasure_tilted_quadraticExponent_of_compact μ hc c Q
  have h2 : MemLp id 2 ((μ : Measure E).tilted (quadraticExponent c Q)) :=
    (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).mpr (hmom c Q 2).1
  have hi := h2.integrable one_le_two
  change (∫ x, (innerSL ℝ h) (id x) ∂((μ : Measure E).tilted (quadraticExponent c Q))) =
    (innerSL ℝ h) (∫ x, id x ∂((μ : Measure E).tilted (quadraticExponent c Q)))
  exact (innerSL ℝ h).integral_comp_comm hi
variable {ι : Type*} [Fintype ι]
end Mean
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
/-- The posterior mean `a(c,Q) = ∫ x dμ_{c,Q}` is jointly `C^∞` (reconstructed from its coordinates in an
orthonormal basis). -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) => FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2) := by
  let b := stdOrthonormalBasis ℝ E
  have hs (i : Fin (Module.finrank ℝ E)) :
      ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) =>
        FunctionalInequalities.Probability.Posterior.posteriorExpectation μ p.1 p.2 (fun x => ⟪b i, x⟫)) :=
    FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_joint_of_continuous μ hc (by fun_prop)
  have hm : ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) =>
      ∑ i, FunctionalInequalities.Probability.Posterior.posteriorExpectation μ p.1 p.2 (fun x => ⟪b i, x⟫) • b i) :=
    ContDiff.sum (fun i _hi => (hs i).smul contDiff_const)
  have he : (fun p : E × (E →L[ℝ] E) => FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2) =
      fun p => ∑ i, FunctionalInequalities.Probability.Posterior.posteriorExpectation μ p.1 p.2 (fun x => ⟪b i, x⟫) • b i := by
    funext p
    rw [← b.sum_repr' (FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2)]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← FunctionalInequalities.Probability.Posterior.integral_inner_eq_inner_posteriorMean μ hc p.1 p.2 (b i)]
    rfl
  rw [he]
  exact hm
