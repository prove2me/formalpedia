-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.bilinearIteratedFDerivTwo_posteriorExpectation_c_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:29:29.502209+00:00
-- url     : https://prove2.me/submissions/106eae88-2ca1-45f4-972a-f0263f693966

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Generator
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_posteriorExpectation_c_readable
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_covariance_hasDerivAt_of_compact_readable
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_fderiv_posteriorExpectation_c_apply_readable

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section Smooth
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem FunctionalInequalities.Probability.Posterior.line_hasDerivAt (c h : E) : HasDerivAt (fun t : ℝ => c + t • h) h 0 := by
  convert! ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add c using 1
  simp only [one_smul]
/-- The `c`-Hessian of the posterior expectation: `Cov(f, ⟪h,x⟫⟪k,x⟫) − (∫⟪h,x⟫) Cov(f,⟪k,x⟫) − (∫⟪k,x⟫) Cov(f,⟪h,x⟫)`. -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C)
    (c : E) (Q : E →L[ℝ] E) (h k : E) :
    bilinearIteratedFDerivTwo ℝ (fun y => FunctionalInequalities.Probability.Posterior.posteriorExpectation μ y Q f) c h k =
      covariance f (fun x => ⟪h, x⟫ * ⟪k, x⟫) ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q)) -
        (∫ x, ⟪h, x⟫ ∂((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q))) *
          covariance f (fun x => ⟪k, x⟫) ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q)) -
        (∫ x, ⟪k, x⟫ ∂((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q))) *
          covariance f (fun x => ⟪h, x⟫) ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q)) := by
  have hsm := FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_c_readable μ hc hf hC hfb Q
  have hsm2 : ContDiff ℝ 2 (fun y => FunctionalInequalities.Probability.Posterior.posteriorExpectation μ y Q f) := hsm.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_eq_fderiv_apply hsm2]
  have hD := (FunctionalInequalities.Analysis.BakryEmery.differentiable_fderiv_apply hsm2 k c).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) (FunctionalInequalities.Probability.Posterior.line_hasDerivAt c h) (by simp)
  have hφ : Continuous (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q) := by unfold FunctionalInequalities.Probability.Posterior.quadraticExponent; fun_prop
  have hh : Continuous (fun x : E => ⟪h, x⟫) := by fun_prop
  have hk : Continuous (fun x : E => ⟪k, x⟫) := by fun_prop
  have hN := FunctionalInequalities.Probability.Posterior.covariance_hasDerivAt_of_compact_readable μ hc hφ hh hk hf hC hfb
  have hphase (t : ℝ) : FunctionalInequalities.Probability.Posterior.quadraticExponent (c + t • h) Q =
      fun x => FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x + t * ⟪h, x⟫ := by
    funext x
    simp only [FunctionalInequalities.Probability.Posterior.quadraticExponent, inner_add_left, real_inner_smul_left]
    ring
  have hfun : (fun y => fderiv ℝ (fun z => FunctionalInequalities.Probability.Posterior.posteriorExpectation μ z Q f) y k) =
      fun y => covariance f (fun x => ⟪k, x⟫) ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent y Q)) := by
    funext y
    exact FunctionalInequalities.Probability.Posterior.fderiv_posteriorExpectation_c_apply_readable μ hc hf hC hfb y Q k
  have hD' := hD
  simp only [Function.comp_def, hfun, hphase] at hD'
  simpa only [hfun] using hD'.unique hN
