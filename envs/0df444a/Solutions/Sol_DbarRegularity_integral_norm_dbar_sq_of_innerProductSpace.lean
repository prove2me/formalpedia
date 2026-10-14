-- Prove2me | solution 1 for DbarRegularity.integral_norm_dbar_sq_of_innerProductSpace
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T22:20:48.970658+00:00
-- url     : https://prove2.me/submissions/4001b422-8272-44e5-b22a-18c839344e7c

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Symmetric



namespace DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

theorem integral_norm_dbar_sq_of_innerProductSpace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (φ : ℂ → E) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∫ z, ‖dbar φ z‖ ^ 2 = (∫ z, ‖fderiv ℝ φ z 1‖ ^ 2) + ∫ z, ‖fderiv ℝ φ z Complex.I‖ ^ 2 := by
  -- the real-bilinear form `B u w = Re ⟪u, i w⟫`
  let B : E →L[ℝ] E →L[ℝ] ℝ := LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun u w : E => (inner ℂ u (Complex.I • w)).re)
      (fun u u' w => by simp [inner_add_left])
      (fun c u w => by
        rw [← Complex.coe_smul, inner_smul_left]
        simp [Complex.mul_re])
      (fun u w w' => by simp [smul_add, inner_add_right])
      (fun c u w => by
        rw [← Complex.coe_smul, smul_comm, inner_smul_right]
        simp [Complex.mul_re]))
    1 (fun u w => by
      simp only [LinearMap.mk₂_apply, Real.norm_eq_abs, one_mul]
      refine (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
      rw [norm_smul, Complex.norm_I, one_mul])
  have hB : ∀ u w, B u w = (inner ℂ u (Complex.I • w)).re := fun u w => rfl
  have hBanti : ∀ u w, B u w = - B w u := by
    intro u w
    rw [hB, hB, inner_smul_right, inner_smul_right]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
    rw [← inner_conj_symm w u, Complex.conj_im]
    ring
  -- regularity
  have hd1 : ContDiff ℝ ∞ (fderiv ℝ φ) := (contDiff_infty_iff_fderiv.1 hφ).2
  have hcd : HasCompactSupport (fderiv ℝ φ) := hc.fderiv ℝ
  have hps_c : ContDiff ℝ ∞ (fun z => fderiv ℝ φ z 1) := hd1.clm_apply contDiff_const
  have hpt_c : ContDiff ℝ ∞ (fun z => fderiv ℝ φ z Complex.I) := hd1.clm_apply contDiff_const
  have hcps : HasCompactSupport (fun z => fderiv ℝ φ z 1) :=
    hcd.mono' (fun z hz => subset_tsupport _ (fun h => hz (by simp [h])))
  have hcpt : HasCompactSupport (fun z => fderiv ℝ φ z Complex.I) :=
    hcd.mono' (fun z hz => subset_tsupport _ (fun h => hz (by simp [h])))
  have hdiff : ∀ z, DifferentiableAt ℝ (fderiv ℝ φ) z :=
    fun z => (hd1.differentiable (by simp)) z
  have hsymm : ∀ z, fderiv ℝ (fun y => fderiv ℝ φ y Complex.I) z 1
      = fderiv ℝ (fun y => fderiv ℝ φ y 1) z Complex.I := by
    intro z
    have h1 : ∀ v w, fderiv ℝ (fun y => fderiv ℝ φ y v) z w = fderiv ℝ (fderiv ℝ φ) z w v := by
      intro v w
      rw [fderiv_clm_apply (hdiff z) (differentiableAt_const v)]
      simp
    have hs : IsSymmSndFDerivAt ℝ φ z :=
      (hφ.contDiffAt).isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; first | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)) | decide)
    rw [h1, h1, hs.eq]
  -- integrability
  have hint : ∀ f g : ℂ → E, Continuous f → Continuous g → HasCompactSupport f →
      Integrable (fun z => B (f z) (g z)) := by
    intro f g hf hg hcf
    apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
    exact hcf.mono' (fun z hz => subset_tsupport _ (fun h => hz (by simp [h])))
  have hcont_ps := hps_c.continuous
  have hcont_pt := hpt_c.continuous
  have hdiffφ : ∀ z, DifferentiableAt ℝ φ z := fun z => (hφ.differentiable (by simp)) z
  have hdiffpt : ∀ z, DifferentiableAt ℝ (fun z => fderiv ℝ φ z Complex.I) z :=
    fun z => (hpt_c.differentiable (by simp)) z
  have hdiffps : ∀ z, DifferentiableAt ℝ (fun z => fderiv ℝ φ z 1) z :=
    fun z => (hps_c.differentiable (by simp)) z
  -- integration by parts in the directions `1` and `i`
  have ibp1 : ∫ z, B (φ z) (fderiv ℝ (fun y => fderiv ℝ φ y Complex.I) z 1)
      = - ∫ z, B (fderiv ℝ φ z 1) (fderiv ℝ φ z Complex.I) :=
    integral_bilinear_fderiv_right_eq_neg_left_of_integrable (v := 1)
      (hint _ _ hcont_ps hcont_pt hcps)
      (hint _ _ hφ.continuous ((hpt_c.continuous_fderiv (by simp)).clm_apply continuous_const) hc)
      (hint _ _ hφ.continuous hcont_pt hc)
      (fun z _ => hdiffφ z) (fun z _ => hdiffpt z)
  have ibp2 : ∫ z, B (φ z) (fderiv ℝ (fun y => fderiv ℝ φ y 1) z Complex.I)
      = - ∫ z, B (fderiv ℝ φ z Complex.I) (fderiv ℝ φ z 1) :=
    integral_bilinear_fderiv_right_eq_neg_left_of_integrable (v := Complex.I)
      (hint _ _ hcont_pt hcont_ps hcpt)
      (hint _ _ hφ.continuous ((hps_c.continuous_fderiv (by simp)).clm_apply continuous_const) hc)
      (hint _ _ hφ.continuous hcont_ps hc)
      (fun z _ => hdiffφ z) (fun z _ => hdiffps z)
  have hcross : ∫ z, B (fderiv ℝ φ z 1) (fderiv ℝ φ z Complex.I) = 0 := by
    have e1 : ∫ z, B (φ z) (fderiv ℝ (fun y => fderiv ℝ φ y Complex.I) z 1)
        = ∫ z, B (φ z) (fderiv ℝ (fun y => fderiv ℝ φ y 1) z Complex.I) := by
      simp_rw [hsymm]
    have e2 : ∫ z, B (fderiv ℝ φ z Complex.I) (fderiv ℝ φ z 1)
        = - ∫ z, B (fderiv ℝ φ z 1) (fderiv ℝ φ z Complex.I) := by
      rw [← integral_neg]; simp_rw [hBanti (fderiv ℝ φ _ Complex.I)]
    linarith
  -- pointwise expansion
  have hpw : ∀ z, ‖dbar φ z‖ ^ 2 = ‖fderiv ℝ φ z 1‖ ^ 2 + ‖fderiv ℝ φ z Complex.I‖ ^ 2
      + 2 * B (fderiv ℝ φ z 1) (fderiv ℝ φ z Complex.I) := by
    intro z
    simp only [dbar, hB]
    rw [norm_add_sq (𝕜 := ℂ), norm_smul, Complex.norm_I, one_mul, RCLike.re_to_complex]
    ring
  have hsq : ∀ f : ℂ → E, Continuous f → HasCompactSupport f →
      Integrable (fun z => ‖f z‖ ^ 2) := by
    intro f hf hcf
    apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
    exact hcf.mono' (fun z hz => subset_tsupport _ (fun h => hz (by simp [h])))
  rw [show (fun z => ‖dbar φ z‖ ^ 2) = (fun z => ‖fderiv ℝ φ z 1‖ ^ 2
      + ‖fderiv ℝ φ z Complex.I‖ ^ 2 + 2 * B (fderiv ℝ φ z 1) (fderiv ℝ φ z Complex.I))
      from funext hpw]
  have i1 := hsq _ hcont_ps hcps
  have i2 := hsq _ hcont_pt hcpt
  have i3 := (hint _ _ hcont_ps hcont_pt hcps).const_mul 2
  have i12 : Integrable (fun z => ‖fderiv ℝ φ z 1‖ ^ 2 + ‖fderiv ℝ φ z Complex.I‖ ^ 2) :=
    i1.add i2
  rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, hcross, mul_zero, add_zero]

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (φ : ℂ → E) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    ∫ z, ‖dbar φ z‖ ^ 2 = (∫ z, ‖fderiv ℝ φ z 1‖ ^ 2) + ∫ z, ‖fderiv ℝ φ z Complex.I‖ ^ 2 :=
  integral_norm_dbar_sq_of_innerProductSpace φ hφ hc
