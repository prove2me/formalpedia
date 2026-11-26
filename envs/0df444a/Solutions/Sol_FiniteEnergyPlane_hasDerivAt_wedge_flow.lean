-- Prove2me | solution 1 for FiniteEnergyPlane.hasDerivAt_wedge_flow
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-26T21:22:16.860063+00:00
-- url     : https://prove2.me/submissions/da915dcb-d78e-4ff6-a16f-6837b13dbfbe

import Mathlib
import Theorems.Thm_FlowCalculus_spatial_differential_hasDerivAt



/-! Child B of P c5a21fab: `hasDerivAt_wedge_flow`. -/

namespace FiniteEnergyPlane

open scoped ContDiff

theorem olpb_hasDerivAt_re {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => (f s).re) f'.re t := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h

theorem olpb_hasDerivAt_im {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => (f s).im) f'.im t := by
  exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h

theorem olpb_apply (L : ℂ →L[ℝ] ℂ) (a : ℂ) : L a = a.re • L 1 + a.im • L Complex.I := by
  have ha : a = a.re • (1 : ℂ) + a.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [ha]
  rw [map_add, map_smul, map_smul]

theorem hasDerivAt_wedge_flow_aux (X : ℂ → ℂ) (hX : ContDiff ℝ ∞ X) (ψ : ℝ → ℂ → ℂ)
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × ℂ => ψ p.1 p.2))
    (hflow : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t) (t : ℝ) (y w : ℂ) :
    HasDerivAt (fun s => (X (ψ s y)).re * (fderiv ℝ (ψ s) y w).im -
        (X (ψ s y)).im * (fderiv ℝ (ψ s) y w).re)
      (((fderiv ℝ X (ψ t y) 1).re + (fderiv ℝ X (ψ t y) Complex.I).im) *
        ((X (ψ t y)).re * (fderiv ℝ (ψ t) y w).im - (X (ψ t y)).im * (fderiv ℝ (ψ t) y w).re)) t := by
  have hXd : Differentiable ℝ X := hX.differentiable (by simp)
  have hA : HasDerivAt (fun s => X (ψ s y)) (fderiv ℝ X (ψ t y) (X (ψ t y))) t :=
    (hXd (ψ t y)).hasFDerivAt.comp_hasDerivAt t (hflow t y)
  have hB : HasDerivAt (fun s => fderiv ℝ (ψ s) y w)
      (fderiv ℝ X (ψ t y) (fderiv ℝ (ψ t) y w)) t :=
    FlowCalculus.spatial_differential_hasDerivAt (fun _ z => X z) (hX.comp contDiff_snd) ψ hψ
      hflow t y w
  have h := ((olpb_hasDerivAt_re hA).mul (olpb_hasDerivAt_im hB)).sub
    ((olpb_hasDerivAt_im hA).mul (olpb_hasDerivAt_re hB))
  refine h.congr_deriv ?_
  set L := fderiv ℝ X (ψ t y)
  set A := X (ψ t y)
  set B := fderiv ℝ (ψ t) y w
  rw [olpb_apply L A, olpb_apply L B]
  simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

end FiniteEnergyPlane

open FiniteEnergyPlane

open scoped ContDiff

theorem solution (X : ℂ → ℂ) (hX : ContDiff ℝ ∞ X) (ψ : ℝ → ℂ → ℂ)
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × ℂ => ψ p.1 p.2))
    (hflow : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t) (t : ℝ) (y w : ℂ) :
    HasDerivAt (fun s => (X (ψ s y)).re * (fderiv ℝ (ψ s) y w).im -
        (X (ψ s y)).im * (fderiv ℝ (ψ s) y w).re)
      (((fderiv ℝ X (ψ t y) 1).re + (fderiv ℝ X (ψ t y) Complex.I).im) *
        ((X (ψ t y)).re * (fderiv ℝ (ψ t) y w).im - (X (ψ t y)).im * (fderiv ℝ (ψ t) y w).re)) t :=
  hasDerivAt_wedge_flow_aux X hX ψ hψ hflow t y w
