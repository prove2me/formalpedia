-- Prove2me | solution 1 for CohnElkies.lowerGammaScaledPositivePart_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/323dc7da-383f-4646-b71e-8d0b94e404da

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_dimension_scaled_nonpos_of_large

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 2 ≤ d) {c : ℝ} (hc : 0 < c) :
    Function.support (lowerGammaScaledPositivePart d c) ⊆
      Icc (-(max 1 (8 * Real.pi * c ^ 2)))
        (max 1 (8 * Real.pi * c ^ 2)) := by
  intro Y hY
  change lowerGammaScaledPositivePart d c Y ≠ 0 at hY
  have hsmall : |Y| < max 1 (8 * Real.pi * c ^ 2) := by
    by_contra hnot
    have hlarge : max 1 (8 * Real.pi * c ^ 2) ≤ |Y| :=
      le_of_not_gt hnot
    have hnonpos :=
      lowerGammaBoundaryLog_dimension_scaled_nonpos_of_large
        hd hc hlarge
    apply hY
    unfold lowerGammaScaledPositivePart
    exact max_eq_right hnonpos
  exact ⟨(neg_lt_of_abs_lt hsmall).le,
    (lt_of_abs_lt hsmall).le⟩
end CohnElkies
