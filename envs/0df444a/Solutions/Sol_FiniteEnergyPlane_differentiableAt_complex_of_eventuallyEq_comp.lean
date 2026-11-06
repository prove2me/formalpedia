-- Prove2me | solution 1 for FiniteEnergyPlane.differentiableAt_complex_of_eventuallyEq_comp
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-05T20:55:04.478482+00:00
-- url     : https://prove2.me/submissions/ee432b83-0d10-4b68-bcf1-028b29f86fd2

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Complex.Conformal

open Filter Topology

namespace FiniteEnergyPlane

theorem differentiableAt_complex_of_eventuallyEq_comp_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (J : E → E →L[ℝ] E) (u v : ℂ → E) (φ : ℂ → ℂ) (z : ℂ)
    (hJ2 : (J (u z)).comp (J (u z)) = -ContinuousLinearMap.id ℝ E)
    (hφ : DifferentiableAt ℝ φ z) (hv : DifferentiableAt ℝ v (φ z))
    (heq : u =ᶠ[𝓝 z] v ∘ φ)
    (huh : fderiv ℝ u z 1 + J (u z) (fderiv ℝ u z Complex.I) = 0)
    (hvh : fderiv ℝ v (φ z) 1 + J (v (φ z)) (fderiv ℝ v (φ z) Complex.I) = 0)
    (hvi : Function.Injective (fderiv ℝ v (φ z))) :
    DifferentiableAt ℂ φ z := by
  have huz : u z = v (φ z) := heq.self_of_nhds
  rw [← huz] at hvh
  set J₀ := J (u z) with hJ₀
  set D := fderiv ℝ v (φ z) with hD
  set L := fderiv ℝ φ z with hL
  have hJJ : ∀ x, J₀ (J₀ x) = -x := fun x => by
    have := congrArg (fun T => T x) hJ2
    simpa using this
  -- the derivative of `u`
  have hdu : fderiv ℝ u z = D.comp L := by
    rw [heq.fderiv_eq]
    exact (hv.hasFDerivAt.comp z hφ.hasFDerivAt).fderiv
  -- `D` intertwines `i` and `J₀`
  have h1 : J₀ (D 1) = D Complex.I := by
    have : D 1 = -J₀ (D Complex.I) := eq_neg_of_add_eq_zero_left hvh
    rw [this, map_neg, hJJ, neg_neg]
  have h2 : J₀ (D Complex.I) = -D 1 := by rw [← h1, hJJ]
  have ha : ∀ b : ℂ, D b = b.re • D 1 + b.im • D Complex.I := fun b => by
    conv_lhs => rw [← Complex.re_add_im b]
    have : (b.re : ℂ) + (b.im : ℂ) * Complex.I = b.re • (1 : ℂ) + b.im • Complex.I := by
      simp [Complex.real_smul]
    rw [this, map_add, map_smul, map_smul]
  have hDI : ∀ a : ℂ, D (Complex.I * a) = J₀ (D a) := fun a => by
    rw [ha (Complex.I * a), ha a, map_add, map_smul, map_smul, h1, h2]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
      Complex.mul_im, add_zero, zero_add, neg_smul, smul_neg]
    abel
  -- the Cauchy-Riemann equation for `φ`
  have hu1 : D (L 1) = -J₀ (D (L Complex.I)) := by
    have := eq_neg_of_add_eq_zero_left huh
    rw [hdu] at this
    simpa using this
  have hCR : L Complex.I = Complex.I • L 1 := by
    apply hvi
    rw [smul_eq_mul, hDI, hu1, map_neg, hJJ, neg_neg]
  exact differentiableAt_complex_iff_differentiableAt_real.2 ⟨hφ, hCR⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open Filter Topology

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (J : E → E →L[ℝ] E) (u v : ℂ → E) (φ : ℂ → ℂ) (z : ℂ)
    (hJ2 : (J (u z)).comp (J (u z)) = -ContinuousLinearMap.id ℝ E)
    (hφ : DifferentiableAt ℝ φ z) (hv : DifferentiableAt ℝ v (φ z))
    (heq : u =ᶠ[𝓝 z] v ∘ φ)
    (huh : fderiv ℝ u z 1 + J (u z) (fderiv ℝ u z Complex.I) = 0)
    (hvh : fderiv ℝ v (φ z) 1 + J (v (φ z)) (fderiv ℝ v (φ z) Complex.I) = 0)
    (hvi : Function.Injective (fderiv ℝ v (φ z))) :
    DifferentiableAt ℂ φ z :=
  differentiableAt_complex_of_eventuallyEq_comp_aux J u v φ z hJ2 hφ hv heq huh hvh hvi
