-- Prove2me | solution 1 for BookProof.ChapterSphericalPlancherel.sineTransform_odd
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:28:52.884986+00:00
-- url     : https://prove2.me/submissions/92fc6192-8bbe-4b29-ab38-0ba4c6d02bfc

-- Generated from ChapterSphericalPlancherel.lean — solution of BookProof.ChapterSphericalPlancherel.sineTransform_odd
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalPlancherel




open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution (G : ℝ → ℂ) (w : ℝ) :
    sineTransform G (-w) = -sineTransform G w := by

  rw [sineTransform, sineTransform, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [show 2 * π * (x * -w) = -(2 * π * (x * w)) by ring, Real.sin_neg]
  push_cast; ring
