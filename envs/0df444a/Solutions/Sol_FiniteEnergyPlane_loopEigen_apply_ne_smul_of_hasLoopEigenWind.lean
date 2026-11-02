-- Prove2me | solution 1 for FiniteEnergyPlane.loopEigen_apply_ne_smul_of_hasLoopEigenWind
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T21:24:37.207247+00:00
-- url     : https://prove2.me/submissions/d0fe4a45-379b-4689-aabe-9a53847aff5a

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_conj
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_mul
import Theorems.Thm_FiniteEnergyPlane_hasDerivAt_im_conj_mul_loopEigen
import Theorems.Thm_FiniteEnergyPlane_one_le_of_hasLoopWind_of_im_eq_zero



namespace FiniteEnergyPlane

open scoped ContDiff

theorem wls_im_ne_zero (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf) {μ₁ μ₂ : ℝ} {k : ℤ} (hμ : μ₁ < μ₂)
    (h₁ : HasLoopEigenWind Sinf μ₁ k) (h₂ : HasLoopEigenWind Sinf μ₂ k)
    {e₁ e₂ : ℝ → CauchyRiemannIndex.Vec 1} (he₁ : IsLoopEigen Sinf μ₁ e₁)
    (he₂ : IsLoopEigen Sinf μ₂ e₂) (t : ℝ) :
    (starRingEnd ℂ (vecToC (e₁ t)) * vecToC (e₂ t)).im ≠ 0 := by
  intro h0
  have hg := hasLoopWind_mul (hasLoopWind_conj (h₁.2 e₁ he₁)) (h₂.2 e₂ he₂)
  have := one_le_of_hasLoopWind_of_im_eq_zero hg (sub_pos.2 hμ)
    (fun s => hasDerivAt_im_conj_mul_loopEigen Sinf hSinf he₁ he₂ s) h0
  omega

theorem wls_vecToC_smul (c : ℝ) (v : CauchyRiemannIndex.Vec 1) :
    vecToC (c • v) = (c : ℂ) * vecToC v := by
  apply Complex.ext <;> simp [vecToC]

theorem loopEigen_apply_ne_smul_of_hasLoopEigenWind_aux (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) {μ₁ μ₂ : ℝ} {k : ℤ} (hμ : μ₁ ≠ μ₂)
    (h₁ : HasLoopEigenWind Sinf μ₁ k) (h₂ : HasLoopEigenWind Sinf μ₂ k)
    {e₁ e₂ : ℝ → CauchyRiemannIndex.Vec 1} (he₁ : IsLoopEigen Sinf μ₁ e₁)
    (he₂ : IsLoopEigen Sinf μ₂ e₂) (t c : ℝ) : e₂ t ≠ c • e₁ t := by
  intro heq
  have hf : vecToC (e₂ t) = (c : ℂ) * vecToC (e₁ t) := by rw [heq, wls_vecToC_smul]
  rcases hμ.lt_or_gt with hlt | hgt
  · apply wls_im_ne_zero Sinf hSinf hlt h₁ h₂ he₁ he₂ t
    rw [hf]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re]
    ring
  · apply wls_im_ne_zero Sinf hSinf hgt h₂ h₁ he₂ he₁ t
    rw [hf]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, map_mul, Complex.conj_ofReal]
    ring

end FiniteEnergyPlane

open FiniteEnergyPlane

open scoped ContDiff

theorem solution (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) {μ₁ μ₂ : ℝ} {k : ℤ} (hμ : μ₁ ≠ μ₂)
    (h₁ : HasLoopEigenWind Sinf μ₁ k) (h₂ : HasLoopEigenWind Sinf μ₂ k)
    {e₁ e₂ : ℝ → CauchyRiemannIndex.Vec 1} (he₁ : IsLoopEigen Sinf μ₁ e₁)
    (he₂ : IsLoopEigen Sinf μ₂ e₂) (t c : ℝ) : e₂ t ≠ c • e₁ t :=
  loopEigen_apply_ne_smul_of_hasLoopEigenWind_aux Sinf hSinf hSinf' hμ h₁ h₂ he₁ he₂ t c
