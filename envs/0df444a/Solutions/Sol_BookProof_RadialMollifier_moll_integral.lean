-- Prove2me | solution 1 for BookProof.RadialMollifier.moll_integral
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:51:03.414825+00:00
-- url     : https://prove2.me/submissions/262b47a8-0a57-4329-9d68-4fa792fc86f3

-- Generated from ChapterRadialMollifier.lean — solution of BookProof.RadialMollifier.moll_integral
import Mathlib
import Definitions.Def_ChapterRadialMollifier
import Theorems.Thm_BookProof_RadialMollifier_radialMass_pos
open BookProof.RadialMollifier




open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {δ : ℝ} (hδ : 0 < δ) : ∫ z : ℂ, moll δ z = 1 := by

  have hfr : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  have h : ∫ z : ℂ, radialBump (δ⁻¹ • z) = δ ^ 2 • radialMass := by
    rw [MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg volume radialBump hδ.le, hfr,
      radialMass]
  simp only [moll]
  rw [MeasureTheory.integral_div, h, smul_eq_mul]
  have hm := radialMass_pos.ne'
  field_simp
