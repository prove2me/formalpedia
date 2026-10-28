-- Prove2me | solution 1 for FunctionalInequalities.Analysis.hasWeakDerivAlong_of_contDiff_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:29:46.121555+00:00
-- url     : https://prove2.me/submissions/ccf4e519-1f10-4aea-9076-a783522ab3bb

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Basic

noncomputable section
open MeasureTheory
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- A `C¹` function with locally integrable derivative has its classical directional derivative as
weak derivative. -/
theorem solution {f : E → ℝ} (hf : ContDiff ℝ 1 f) (v : E) :
    FunctionalInequalities.Analysis.HasWeakDerivAlong f (fun x => fderiv ℝ f x v) v := by
  refine ⟨hf.continuous.locallyIntegrable, ?_, ?_⟩
  · exact ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).locallyIntegrable
  · intro ψ hψ hψc
    have hψd : Continuous (fun x => fderiv ℝ ψ x v) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψdc : HasCompactSupport (fun x => fderiv ℝ ψ x v) := by
      change HasCompactSupport ((fun L : E →L[ℝ] ℝ => L v) ∘ fderiv ℝ ψ)
      exact (hψc.fderiv ℝ).comp_left (by simp)
    have hf'g : Integrable (fun x => fderiv ℝ f x v * ψ x) (volume : Measure E) := by
      exact
        ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).mul hψ.continuous
          |>.integrable_of_hasCompactSupport hψc.mul_left
    have hfg' : Integrable (fun x => f x * fderiv ℝ ψ x v) (volume : Measure E) := by
      exact (hf.continuous.mul hψd).integrable_of_hasCompactSupport hψdc.mul_left
    have hfg : Integrable (fun x => f x * ψ x) (volume : Measure E) := by
      have hfg₀ : Integrable (fun x => ψ x * f x) (volume : Measure E) :=
        hf.continuous.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
          hψ.continuous hψc
      convert hfg₀ using 1
      funext x
      exact mul_comm _ _
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg' hfg
      (fun x _ => (hf.differentiable (by simp)).differentiableAt)
      (fun x _ => (hψ.differentiable (by simp)).differentiableAt)
