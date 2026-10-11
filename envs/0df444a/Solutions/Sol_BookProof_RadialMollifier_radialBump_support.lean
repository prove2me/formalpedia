-- Prove2me | solution 1 for BookProof.RadialMollifier.radialBump_support
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:49:31.564888+00:00
-- url     : https://prove2.me/submissions/9abff3f1-76be-42d4-9b0b-f54f725e91ca

-- Generated from ChapterRadialMollifier.lean — solution of BookProof.RadialMollifier.radialBump_support
import Mathlib
import Definitions.Def_ChapterRadialMollifier
import Theorems.Thm_BookProof_RadialMollifier_radialBump_eq_zero_of_one_le
import Theorems.Thm_BookProof_RadialMollifier_radialBump_pos_of_lt_one
open BookProof.RadialMollifier




open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution : Function.support radialBump = ball (0 : ℂ) 1 := by

  ext z
  simp only [Function.mem_support, mem_ball, dist_zero_right]
  constructor
  · intro hz
    by_contra hcon
    exact hz (radialBump_eq_zero_of_one_le (not_lt.1 hcon))
  · intro hz
    exact (radialBump_pos_of_lt_one hz).ne'
