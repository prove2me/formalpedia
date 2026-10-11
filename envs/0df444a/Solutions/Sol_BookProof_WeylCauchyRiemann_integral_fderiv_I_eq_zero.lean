-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.integral_fderiv_I_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:39:23.133239+00:00
-- url     : https://prove2.me/submissions/637b5104-c991-4b0e-83d2-19084feef2f8

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.integral_fderiv_I_eq_zero
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Theorems.Thm_BookProof_WeylCauchyRiemann_integral_deriv_eq_zero_of_hasCompactSupport
import Theorems.Thm_BookProof_WeylCauchyRiemann_integral_complex_eq_prod
import Theorems.Thm_BookProof_WeylCauchyRiemann_hasCompactSupport_slice_im
import Theorems.Thm_BookProof_WeylCauchyRiemann_hasCompactSupport_comp_realProd
import Theorems.Thm_BookProof_WeylCauchyRiemann_deriv_slice_im
import Theorems.Thm_BookProof_WeylCauchyRiemann_hasCompactSupport_fderiv_apply
import Theorems.Thm_BookProof_WeylCauchyRiemann_contDiff_slice_im
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) : ∫ z : ℂ, fderiv ℝ ψ z Complex.I = 0 := by

  have hdiff : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hcontF : Continuous fun z : ℂ => fderiv ℝ ψ z Complex.I :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcsF : HasCompactSupport fun z : ℂ => fderiv ℝ ψ z Complex.I :=
    hasCompactSupport_fderiv_apply hψc Complex.I
  rw [integral_complex_eq_prod]
  have hcont : Continuous fun p : ℝ × ℝ => fderiv ℝ ψ ((p.1 : ℂ) + p.2 * Complex.I) Complex.I :=
    hcontF.comp (by fun_prop)
  have hint : Integrable fun p : ℝ × ℝ => fderiv ℝ ψ ((p.1 : ℂ) + p.2 * Complex.I) Complex.I :=
    hcont.integrable_of_hasCompactSupport (hasCompactSupport_comp_realProd hcsF)
  rw [MeasureTheory.Measure.volume_eq_prod, integral_prod _ hint]
  have hinner : ∀ x : ℝ, ∫ y : ℝ, fderiv ℝ ψ ((x : ℂ) + y * Complex.I) Complex.I = 0 := by
    intro x
    have h1 : (fun y : ℝ => fderiv ℝ ψ ((x : ℂ) + y * Complex.I) Complex.I)
        = deriv fun t : ℝ => ψ ((x : ℂ) + t * Complex.I) := by
      funext y
      exact (deriv_slice_im hdiff x y).symm
    rw [h1]
    exact integral_deriv_eq_zero_of_hasCompactSupport
      ((hψ.comp (contDiff_slice_im x)).of_le (by simp))
      (hasCompactSupport_slice_im hψc x)
  simp [hinner]
