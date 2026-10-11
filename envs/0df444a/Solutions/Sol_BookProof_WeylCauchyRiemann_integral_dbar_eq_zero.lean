-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.integral_dbar_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:39:39.038408+00:00
-- url     : https://prove2.me/submissions/4aa8db5e-4316-4fd4-8d81-8133809a7d14

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.integral_dbar_eq_zero
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Theorems.Thm_BookProof_WeylCauchyRiemann_hasCompactSupport_fderiv_apply
import Theorems.Thm_BookProof_WeylCauchyRiemann_integral_fderiv_one_eq_zero
import Theorems.Thm_BookProof_WeylCauchyRiemann_integral_fderiv_I_eq_zero
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) : ∫ z : ℂ, dbar ψ z = 0 := by

  have h1 : Integrable fun z : ℂ => fderiv ℝ ψ z 1 :=
    ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hasCompactSupport_fderiv_apply hψc 1)
  have h2 : Integrable fun z : ℂ => Complex.I * fderiv ℝ ψ z Complex.I := by
    have hc : Continuous fun z : ℂ => Complex.I * fderiv ℝ ψ z Complex.I :=
      continuous_const.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
    exact hc.integrable_of_hasCompactSupport
      (hasCompactSupport_fderiv_apply hψc Complex.I).mul_left
  simp only [dbar]
  rw [integral_add h1 h2, integral_fderiv_one_eq_zero hψ hψc,
    MeasureTheory.integral_const_mul, integral_fderiv_I_eq_zero hψ hψc]
  simp
