-- Prove2me | solution 1 for CohnElkies.lowerGammaScaledCappedClipped_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/97ac3a38-7df7-4f55-999b-af4048a5e625

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaScaledCappedClipped_continuous
import Theorems.Thm_CohnElkies_lowerGammaScaledCappedClipped_support

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
    {d : ℕ} (hd : 2 ≤ d) {c D n : ℝ}
    (hc : 0 < c) (hn : 0 ≤ n) :
    Integrable (lowerGammaScaledCappedClipped d c D n) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  apply (lowerGammaScaledCappedClipped_continuous
    hdpos c D n).integrable_of_hasCompactSupport
  exact HasCompactSupport.of_support_subset_isCompact
    isCompact_Icc
      (lowerGammaScaledCappedClipped_support hd hc hn)
end CohnElkies
