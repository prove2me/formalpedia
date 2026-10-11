-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.integral_fderiv_one_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:39:22.012837+00:00
-- url     : https://prove2.me/submissions/2f6a134b-886b-4c02-b47b-bfb659e66d20

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.integral_fderiv_one_eq_zero
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Theorems.Thm_BookProof_WeylCauchyRiemann_integral_deriv_eq_zero_of_hasCompactSupport
import Theorems.Thm_BookProof_WeylCauchyRiemann_integral_complex_eq_prod
import Theorems.Thm_BookProof_WeylCauchyRiemann_hasCompactSupport_slice_re
import Theorems.Thm_BookProof_WeylCauchyRiemann_hasCompactSupport_comp_realProd
import Theorems.Thm_BookProof_WeylCauchyRiemann_deriv_slice_re
import Theorems.Thm_BookProof_WeylCauchyRiemann_hasCompactSupport_fderiv_apply
import Theorems.Thm_BookProof_WeylCauchyRiemann_contDiff_slice_re
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) : ∫ z : ℂ, fderiv ℝ ψ z 1 = 0 := by

  have hdiff : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hcontF : Continuous fun z : ℂ => fderiv ℝ ψ z 1 :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcsF : HasCompactSupport fun z : ℂ => fderiv ℝ ψ z 1 :=
    hasCompactSupport_fderiv_apply hψc 1
  rw [integral_complex_eq_prod]
  have hcont : Continuous fun p : ℝ × ℝ => fderiv ℝ ψ ((p.1 : ℂ) + p.2 * Complex.I) 1 :=
    hcontF.comp (by fun_prop)
  have hint : Integrable fun p : ℝ × ℝ => fderiv ℝ ψ ((p.1 : ℂ) + p.2 * Complex.I) 1 :=
    hcont.integrable_of_hasCompactSupport (hasCompactSupport_comp_realProd hcsF)
  rw [MeasureTheory.Measure.volume_eq_prod, integral_prod_symm _ hint]
  have hinner : ∀ y : ℝ, ∫ x : ℝ, fderiv ℝ ψ ((x : ℂ) + y * Complex.I) 1 = 0 := by
    intro y
    have h1 : (fun x : ℝ => fderiv ℝ ψ ((x : ℂ) + y * Complex.I) 1)
        = deriv fun t : ℝ => ψ ((t : ℂ) + y * Complex.I) := by
      funext x
      exact (deriv_slice_re hdiff x y).symm
    rw [h1]
    exact integral_deriv_eq_zero_of_hasCompactSupport
      ((hψ.comp (contDiff_slice_re y)).of_le (by simp))
      (hasCompactSupport_slice_re hψc y)
  simp [hinner]
