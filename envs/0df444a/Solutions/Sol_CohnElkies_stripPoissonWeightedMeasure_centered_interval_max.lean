-- Prove2me | solution 1 for CohnElkies.stripPoissonWeightedMeasure_centered_interval_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/dd071101-b88c-4355-a608-ad7f5427e6ef

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_shifted_centered_interval_max
import Theorems.Thm_CohnElkies_stripPoissonWeightedMeasure_apply_Icc

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
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    stripPoissonWeightedMeasure σ s (Icc (-r) r) ≤
      stripPoissonWeightedMeasure σ 0 (Icc (-r) r) := by
  rw [stripPoissonWeightedMeasure_apply_Icc hbelow habove,
    stripPoissonWeightedMeasure_apply_Icc hbelow habove]
  exact ENNReal.ofReal_le_ofReal
    (stripPoissonKernel_shifted_centered_interval_max
      hbelow habove hr s)
end CohnElkies
