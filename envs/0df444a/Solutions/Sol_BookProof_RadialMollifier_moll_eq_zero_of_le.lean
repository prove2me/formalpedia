-- Prove2me | solution 1 for BookProof.RadialMollifier.moll_eq_zero_of_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:49:39.261981+00:00
-- url     : https://prove2.me/submissions/620f3815-d4b9-45c3-a25b-5cc6095c4fef

-- Generated from ChapterRadialMollifier.lean — solution of BookProof.RadialMollifier.moll_eq_zero_of_le
import Mathlib
import Definitions.Def_ChapterRadialMollifier
import Theorems.Thm_BookProof_RadialMollifier_radialBump_eq_zero_of_one_le
open BookProof.RadialMollifier




open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (h : δ ≤ ‖z‖) : moll δ z = 0 := by

  have : (1 : ℝ) ≤ ‖δ⁻¹ • z‖ := by
    rw [norm_smul]
    simp only [norm_inv, Real.norm_eq_abs, abs_of_pos hδ]
    rw [inv_mul_eq_div, le_div_iff₀ hδ]
    simpa using h
  rw [moll, radialBump_eq_zero_of_one_le this, zero_div]
