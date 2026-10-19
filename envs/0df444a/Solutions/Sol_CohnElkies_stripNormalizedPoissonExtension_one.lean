-- Prove2me | solution 1 for CohnElkies.stripNormalizedPoissonExtension_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/ac849fd7-5b14-4312-b5cc-766463f76d69

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution (T : ℝ) :
    stripNormalizedPoissonExtension 1 T =
      limitingStripPoissonDensity T := by
  have hden : Real.cosh (Real.pi * T / 2) + 1 ≠ 0 := by
    linarith [Real.one_le_cosh (Real.pi * T / 2)]
  unfold stripNormalizedPoissonExtension limitingStripPoissonDensity
  simp only [sub_self, mul_zero, zero_div, Real.sinc_zero,
    Real.cos_zero, mul_one]
  field_simp [hden]
end CohnElkies
