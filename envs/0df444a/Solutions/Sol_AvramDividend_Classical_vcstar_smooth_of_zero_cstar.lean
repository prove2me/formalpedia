-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_smooth_of_zero_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:50:56.03636+00:00
-- url     : https://prove2.me/submissions/f918569a-c079-4624-8449-40d67e74b42a

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_affine_nonnegative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution (W : ℝ → ℝ) (hc0 : cstar W = 0) :
    ContDiffOn ℝ 2 (vcstar W) (Ioi 0) := by
  have hlinear :
      ContDiffOn ℝ 2
        (fun z : ℝ => z + barrierValue W 0 0) (Ioi 0) := by
    fun_prop
  apply hlinear.congr
  intro z hz
  have hz0 : 0 ≤ z := le_of_lt hz
  simpa [vcstar, hc0] using
    (barrierValue_zero_affine_nonnegative W z hz0)
