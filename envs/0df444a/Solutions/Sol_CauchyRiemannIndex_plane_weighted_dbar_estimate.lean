-- Prove2me | solution 1 for CauchyRiemannIndex.plane_weighted_dbar_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T11:51:19.773877+00:00
-- url     : https://prove2.me/submissions/f76f5e3d-4ab2-4c79-a222-81abe2362e78

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Theorems.Thm_CauchyRiemannIndex_plane_integral_fderiv_eq_zero
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts



namespace CauchyRiemannIndex

open MeasureTheory

lemma plane_normSq_identity (D z u : ℂ) :
    ‖D + (starRingEnd ℂ) z * (starRingEnd ℂ) u‖ ^ 2 =
      (‖D‖ ^ 2 + ‖z‖ ^ 2 * ‖u‖ ^ 2) + (2 * (z * u * D)).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.re_ofNat,
    Complex.im_ofNat]
  ring

lemma plane_fderiv_mul_sq (u : ℂ → ℂ) (hu : Differentiable ℝ u) (z v : ℂ) :
    fderiv ℝ (fun z => z * u z ^ 2) z v = v * u z ^ 2 + z * (2 * u z * fderiv ℝ u z v) := by
  have h1 : HasFDerivAt (fun z : ℂ => u z * u z) (u z • fderiv ℝ u z + u z • fderiv ℝ u z) z :=
    (hu z).hasFDerivAt.mul (hu z).hasFDerivAt
  have h2 := (hasFDerivAt_id (𝕜 := ℝ) z).mul h1
  have h4 : HasFDerivAt (fun z : ℂ => z * u z ^ 2)
      (id z • (u z • fderiv ℝ u z + u z • fderiv ℝ u z) +
        (u z * u z) • ContinuousLinearMap.id ℝ ℂ) z := by
    exact h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => by simp [sq])
  rw [h4.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.id_apply, id]
  ring

lemma plane_dbar_mul_sq (u : ℂ → ℂ) (hu : Differentiable ℝ u) (z : ℂ) :
    fderiv ℝ (fun z => z * u z ^ 2) z 1 + Complex.I * fderiv ℝ (fun z => z * u z ^ 2) z Complex.I =
      2 * (z * u z * (fderiv ℝ u z 1 + Complex.I * fderiv ℝ u z Complex.I)) := by
  rw [plane_fderiv_mul_sq u hu, plane_fderiv_mul_sq u hu]
  have : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (u z ^ 2) * this

lemma plane_integral_dbar_eq_zero (g : ℂ → ℂ) (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) :
    ∫ z, fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I = 0 := by
  have h1 : Integrable fun z => fderiv ℝ g z 1 :=
    ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hc (fun z hz => by simp [fderiv_of_notMem_tsupport ℝ hz]))
  have h2 : Integrable fun z => Complex.I * fderiv ℝ g z Complex.I :=
    (continuous_const.mul ((hg.continuous_fderiv one_ne_zero).clm_apply
      continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hc (fun z hz => by simp [fderiv_of_notMem_tsupport ℝ hz]))
  rw [integral_add h1 h2, integral_const_mul, plane_integral_fderiv_eq_zero g hg hc,
    plane_integral_fderiv_eq_zero g hg hc]
  simp

lemma plane_dbar_continuous (g : ℂ → ℂ) (hg : ContDiff ℝ 1 g) :
    Continuous fun z => fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I :=
  ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const).add
    (continuous_const.mul ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const))

lemma plane_dbar_hasCompactSupport (g : ℂ → ℂ) (hc : HasCompactSupport g) :
    HasCompactSupport fun z => fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I :=
  HasCompactSupport.intro hc (fun z hz => by simp [fderiv_of_notMem_tsupport ℝ hz])

/-- Weighted estimate for `∂̄ u + z̄ ū` on compactly supported `C¹` maps `ℂ → ℂ`. -/
theorem plane_weighted_dbar_estimate_aux (u : ℂ → ℂ) (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) :
    ∫ z, ‖z‖ ^ 2 * ‖u z‖ ^ 2 ≤
      ∫ z, ‖fderiv ℝ u z 1 + Complex.I * fderiv ℝ u z Complex.I +
        (starRingEnd ℂ) z * (starRingEnd ℂ) (u z)‖ ^ 2 := by
  have hud : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hgC : ContDiff ℝ 1 (fun z : ℂ => z * u z ^ 2) :=
    ContDiff.mul (f := fun z : ℂ => z) contDiff_id (hu.pow 2)
  have hgc : HasCompactSupport (fun z : ℂ => z * u z ^ 2) :=
    HasCompactSupport.intro hc (fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz])
  have hkey : ∀ z, ‖fderiv ℝ u z 1 + Complex.I * fderiv ℝ u z Complex.I +
        (starRingEnd ℂ) z * (starRingEnd ℂ) (u z)‖ ^ 2 =
      (‖fderiv ℝ u z 1 + Complex.I * fderiv ℝ u z Complex.I‖ ^ 2 + ‖z‖ ^ 2 * ‖u z‖ ^ 2) +
        (fderiv ℝ (fun z => z * u z ^ 2) z 1 +
          Complex.I * fderiv ℝ (fun z => z * u z ^ 2) z Complex.I).re := by
    intro z
    rw [plane_dbar_mul_sq u hud z]
    exact plane_normSq_identity _ _ _
  have hint1 : Integrable fun z => ‖fderiv ℝ u z 1 + Complex.I * fderiv ℝ u z Complex.I‖ ^ 2 :=
    ((plane_dbar_continuous u hu).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hc (fun z hz => by simp [fderiv_of_notMem_tsupport ℝ hz]))
  have hint2 : Integrable fun z : ℂ => ‖z‖ ^ 2 * ‖u z‖ ^ 2 :=
    ((continuous_norm.pow 2).mul (hu.continuous.norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hc (fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]))
  have hint3 := (plane_dbar_continuous _ hgC).integrable_of_hasCompactSupport (μ := volume)
    (plane_dbar_hasCompactSupport _ hgc)
  have hre : ∫ z, (fderiv ℝ (fun z => z * u z ^ 2) z 1 +
      Complex.I * fderiv ℝ (fun z => z * u z ^ 2) z Complex.I).re = 0 := by
    have := integral_re (𝕜 := ℂ) hint3
    simp only [RCLike.re_to_complex] at this
    rw [this, plane_integral_dbar_eq_zero _ hgC hgc]; simp
  set A : ℂ → ℝ := fun z => ‖fderiv ℝ u z 1 + Complex.I * fderiv ℝ u z Complex.I‖ ^ 2 with hA
  set B : ℂ → ℝ := fun z => ‖z‖ ^ 2 * ‖u z‖ ^ 2 with hB
  set C : ℂ → ℝ := fun z => (fderiv ℝ (fun z => z * u z ^ 2) z 1 +
      Complex.I * fderiv ℝ (fun z => z * u z ^ 2) z Complex.I).re with hC
  have hint3' : Integrable C := hint3.re
  calc ∫ z, B z ≤ ∫ z, (A z + B z) :=
        integral_mono hint2 (hint1.add hint2) (fun z => by
          show B z ≤ A z + B z
          have : 0 ≤ A z := by positivity
          linarith)
    _ = (∫ z, (A z + B z)) + ∫ z, C z := by rw [hre, add_zero]
    _ = ∫ z, ((A z + B z) + C z) := (integral_add (hint1.add hint2) hint3').symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun z => (hkey z).symm)

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory

theorem solution (u : ℂ → ℂ) (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) :
    ∫ z, ‖z‖ ^ 2 * ‖u z‖ ^ 2 ≤
      ∫ z, ‖fderiv ℝ u z 1 + Complex.I * fderiv ℝ u z Complex.I +
        (starRingEnd ℂ) z * (starRingEnd ℂ) (u z)‖ ^ 2 :=
  plane_weighted_dbar_estimate_aux u hu hc
