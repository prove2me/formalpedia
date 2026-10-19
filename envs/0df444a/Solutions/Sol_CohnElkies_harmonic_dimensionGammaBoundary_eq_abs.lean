-- Prove2me | solution 1 for CohnElkies.harmonic_dimensionGammaBoundary_eq_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/478c0002-4223-43a0-bf02-ab5a530fc1f8

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_dimension_neg

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog ((d : ℝ) / 2) R y =
      lowerGammaBoundaryLog ((d : ℝ) / 2) R |y| := by
  by_cases hnonneg : 0 ≤ y
  · rw [abs_of_nonneg hnonneg]
  · have hneg : y < 0 := lt_of_not_ge hnonneg
    rw [abs_of_neg hneg]
    exact
      (lowerGammaBoundaryLog_dimension_neg
        (d := d) R hy).symm
end CohnElkies
