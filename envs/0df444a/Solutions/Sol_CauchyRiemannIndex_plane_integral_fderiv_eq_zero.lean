-- Prove2me | solution 1 for CauchyRiemannIndex.plane_integral_fderiv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T11:50:27.642197+00:00
-- url     : https://prove2.me/submissions/ce21c26d-1f60-4895-8d93-13d57903b391

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts



namespace CauchyRiemannIndex

open MeasureTheory

/-- The integral over `ℂ` of a directional derivative of a compactly supported `C¹` function
vanishes. -/
theorem plane_integral_fderiv_eq_zero_aux (g : ℂ → ℂ) (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (v : ℂ) : ∫ z, fderiv ℝ g z v = 0 := by
  have hcont : Continuous fun z => fderiv ℝ g z v :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcs : HasCompactSupport fun z => fderiv ℝ g z v :=
    HasCompactSupport.intro hc (fun z hz => by simp [fderiv_of_notMem_tsupport ℝ hz])
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : ℂ => (1 : ℂ)) (g := g) (v := v)
    (by simp) (by simpa using hcont.integrable_of_hasCompactSupport hcs)
    (by simpa using hg.continuous.integrable_of_hasCompactSupport hc)
    (fun x _ => differentiableAt_const _)
    (fun x _ => (hg.differentiable one_ne_zero) x)
  simpa using h

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory

theorem solution (g : ℂ → ℂ) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (v : ℂ) :
    ∫ z, fderiv ℝ g z v = 0 :=
  plane_integral_fderiv_eq_zero_aux g hg hc v
