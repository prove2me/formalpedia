-- Prove2me | solution 1 for BookProof.ChapterSphericalPlancherel.sineKernelTransform_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:28:58.315653+00:00
-- url     : https://prove2.me/submissions/01c265fa-ee36-4f4d-9fc8-5f037ddacb14

-- Generated from ChapterSphericalPlancherel.lean — solution of BookProof.ChapterSphericalPlancherel.sineKernelTransform_eq
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalPlancherel




open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution (G : ℝ → ℂ) (p : ℝ) :
    sineKernelTransform G p = sineTransform G ((2 * π)⁻¹ * p) := by

  rw [sineKernelTransform, sineTransform]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  congr 3
  field_simp
