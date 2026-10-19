-- Prove2me | solution 1 for CohnElkies.lowerGammaScaledCappedClipped_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/a4deeeef-aca1-45b7-bd1c-16e063c8795c

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_dimension_scaled_le_neg_of_large

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
    Function.support (lowerGammaScaledCappedClipped d c D n) ⊆
      Icc (-(max 1 (8 * Real.pi * c ^ 2 * Real.exp n)))
        (max 1 (8 * Real.pi * c ^ 2 * Real.exp n)) := by
  intro Y hY
  change lowerGammaScaledCappedClipped d c D n Y ≠ 0 at hY
  have hsmall : |Y| < max 1 (8 * Real.pi * c ^ 2 * Real.exp n) := by
    by_contra hnot
    have hlarge : max 1
        (8 * Real.pi * c ^ 2 * Real.exp n) ≤ |Y| :=
      le_of_not_gt hnot
    have hnonpos :=
      lowerGammaBoundaryLog_dimension_scaled_le_neg_of_large
        hd hc hn hlarge
    have hyone : 1 ≤ |Y| :=
      le_trans (le_max_left 1 _) hlarge
    have hyzero : Y ≠ 0 := by
      intro hzero
      norm_num [hzero] at hyone
    have hℓ : 0 < (d : ℝ) / 2 := by
      positivity
    have harg : ((d : ℝ) / 2) * Y ≠ 0 :=
      mul_ne_zero hℓ.ne' hyzero
    apply hY
    unfold lowerGammaScaledCappedClipped
    rw [lowerGammaBoundaryCapped, if_neg harg]
    apply max_eq_right
    have hmin := min_le_left
      (lowerGammaBoundaryLog ((d : ℝ) / 2)
        (c * Real.sqrt d) (((d : ℝ) / 2) * Y)) D
    linarith
  exact ⟨(neg_lt_of_abs_lt hsmall).le,
    (lt_of_abs_lt hsmall).le⟩
end CohnElkies
