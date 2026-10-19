-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryCapped_dimension_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/f0dd1048-6783-4b9c-9647-7ba13232e34d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_dimension_neg

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (R D y : ℝ) :
    lowerGammaBoundaryCapped ((d : ℝ) / 2) R D (-y) =
      lowerGammaBoundaryCapped ((d : ℝ) / 2) R D y := by
  by_cases hy : y = 0
  · simp [lowerGammaBoundaryCapped, hy]
  · simp [lowerGammaBoundaryCapped, hy,
      lowerGammaBoundaryLog_dimension_neg R hy]
end CohnElkies
