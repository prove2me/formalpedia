-- Prove2me | solution 1 for BookProof.ChapterSphericalPlancherel.sineKernel_plancherel
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:28:59.648909+00:00
-- url     : https://prove2.me/submissions/62b7cc5e-27c6-4521-9e33-0c871f9b979c

-- Generated from ChapterSphericalPlancherel.lean — solution of BookProof.ChapterSphericalPlancherel.sineKernel_plancherel
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
import Theorems.Thm_BookProof_ChapterSphericalPlancherel_sine_plancherel
import Theorems.Thm_BookProof_ChapterSphericalPlancherel_sineKernelTransform_eq
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalPlancherel




open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution (G : 𝓢(ℝ, ℂ)) (hodd : ∀ x, G (-x) = -G x) :
    ∫ p in Ioi (0 : ℝ), ‖sineKernelTransform (⇑G) p‖ ^ 2
      = (π / 2) * ∫ x in Ioi (0 : ℝ), ‖G x‖ ^ 2 := by

  have hpi : (0 : ℝ) < (2 * π)⁻¹ := by positivity
  have hsub : ∫ p in Ioi (0 : ℝ), ‖sineTransform (⇑G) ((2 * π)⁻¹ * p)‖ ^ 2
      = (2 * π) * ∫ w in Ioi (0 : ℝ), ‖sineTransform (⇑G) w‖ ^ 2 := by
    have hcv := integral_comp_mul_left_Ioi
      (fun w : ℝ => ‖sineTransform (⇑G) w‖ ^ 2) (0 : ℝ) hpi
    rw [hcv]
    simp only [mul_zero, smul_eq_mul, inv_inv]
  simp_rw [sineKernelTransform_eq]
  rw [hsub, sine_plancherel G hodd]
  ring
