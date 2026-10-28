-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.norm_posteriorMean_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:28:37.427986+00:00
-- url     : https://prove2.me/submissions/b2867925-6b69-4070-942d-b2ebf1844d6d

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactDomain
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Bound

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
universe u v
section TiltAbsoluteContinuity
variable {Ω : Type*} [MeasurableSpace Ω]
/-- A normalized tilt has the same a.e. filter as the base law. -/
theorem FunctionalInequalities.Probability.ae_tilted_eq (μ : Measure Ω) {φ : Ω → ℝ}
    (hi : Integrable (fun x => Real.exp (φ x)) μ) : ae (μ.tilted φ) = ae μ :=
  le_antisymm (tilted_absolutelyContinuous μ φ).ae_le (absolutelyContinuous_tilted hi).ae_le
end TiltAbsoluteContinuity
end
end
end

section
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The posterior has the same a.e. filter as the prior. -/
theorem FunctionalInequalities.Probability.Posterior.compactPosterior_ae (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) :
    ae (compactPosterior μ hc c Q : Measure E) = ae (μ : Measure E) := by
  exact Probability.ae_tilted_eq _ (integrable_exp_of_compact μ hc (by unfold quadraticExponent; fun_prop))
end
end
end

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery
variable {n : ℕ}
variable (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
/-- The posterior mean lies in the ball carrying the prior. -/
theorem solution {r : ℝ} (hr : 0 ≤ r)
    (hsupp : (μ : Measure (EuclideanSpace ℝ (Fin n))).support ⊆ Metric.closedBall 0 r) (p : FunctionalInequalities.KLS.BKL.Localization.Param n) :
    ‖FunctionalInequalities.Probability.Posterior.posteriorMean μ p.1 p.2‖ ≤ r := by
  have hc' : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) r).of_isClosed_subset
      Measure.isClosed_support hsupp
  have hae : ∀ᵐ x ∂(FunctionalInequalities.Probability.Posterior.compactPosterior μ hc' p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))),
      ‖x‖ ≤ max r 0 := by
    rw [FunctionalInequalities.Probability.Posterior.compactPosterior_ae μ hc' p.1 p.2]
    filter_upwards [Measure.support_mem_ae
      (μ := (μ : Measure (EuclideanSpace ℝ (Fin n))))] with x hx
    exact (mem_closedBall_zero_iff.mp (hsupp hx)).trans (le_max_left r 0)
  have hb :
      ‖∫ x, x ∂(FunctionalInequalities.Probability.Posterior.compactPosterior μ hc' p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))‖ ≤ r := by
    simpa [max_eq_left hr] using norm_integral_le_of_norm_le_const hae
  change ‖∫ x, x ∂((μ : Measure (EuclideanSpace ℝ (Fin n))).tilted
    (FunctionalInequalities.Probability.Posterior.quadraticExponent p.1 p.2))‖ ≤ r
  exact hb
