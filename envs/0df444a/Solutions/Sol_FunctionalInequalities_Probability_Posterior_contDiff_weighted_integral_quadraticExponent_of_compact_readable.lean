-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.contDiff_weighted_integral_quadraticExponent_of_compact_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:04:39.379988+00:00
-- url     : https://prove2.me/submissions/db424705-96f5-4ab1-9d25-ad7b5effdbd7

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Generator
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_integrable_exp_norm_mul_of_compact_readable

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section Smooth
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The unnormalized integral `c ↦ ∫ e^{E_{c,Q}} f dμ` is `C^∞` under a compact prior (weighted-integral
smoothness inside every exponential radius). -/
theorem solution (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) (Q : E →L[ℝ] E) :
    ContDiff ℝ ∞ (fun c : E => ∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x) * f x ∂(μ : Measure E)) := by
  let g : E → ℝ := fun x => Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent 0 Q x) * f x
  have hp : Continuous (FunctionalInequalities.Probability.Posterior.quadraticExponent (0 : E) Q) := by unfold FunctionalInequalities.Probability.Posterior.quadraticExponent; fun_prop
  have hg : AEStronglyMeasurable g (μ : Measure E) := (Real.continuous_exp.comp hp).aestronglyMeasurable.mul hf.aestronglyMeasurable
  have hi (s : ℝ) : Integrable (fun x => Real.exp (s * ‖x‖) * ‖g x‖) (μ : Measure E) :=
    FunctionalInequalities.Probability.Posterior.integrable_exp_norm_mul_of_compact_readable μ hc hf hC hfb Q s
  have hs : ContDiff ℝ ∞ (fun c : E => ∫ x, Real.exp ⟪c, x⟫ • g x ∂(μ : Measure E)) := by
    rw [contDiff_iff_contDiffAt]
    intro c
    have hon := FunctionalInequalities.Analysis.BakryEmery.weighted_integral_contDiffOn (μ : Measure E) hg
      (r := ‖c‖ + 1) (fun s _hs => hi s)
    apply hon.contDiffAt
    exact Metric.isOpen_ball.mem_nhds (by simpa only [Metric.mem_ball, dist_zero_right] using (lt_add_one ‖c‖))
  have heq : (fun c : E => ∫ x, Real.exp ⟪c, x⟫ • g x ∂(μ : Measure E)) =
      fun c => ∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x) * f x ∂(μ : Measure E) := by
    funext c
    congr 1
    funext x
    dsimp [g]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    simp only [FunctionalInequalities.Probability.Posterior.quadraticExponent, inner_zero_left, zero_sub]
    ring
  rw [heq] at hs
  exact hs
