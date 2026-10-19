-- Prove2me | solution 1 for CohnElkies.complexFrullaniSegment_min_re_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/a098fd9c-b72e-4883-bbf3-caff748102cc

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (z w : ℂ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    min z.re w.re ≤ (complexFrullaniSegment z w s).re := by
  simp only [complexFrullaniSegment, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, zero_mul, sub_zero]
  have hzmin := min_le_left z.re w.re
  have hwmin := min_le_right z.re w.re
  have hfirst :
      0 ≤ (1 - s) * (z.re - min z.re w.re) :=
    mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hzmin)
  have hsecond :
      0 ≤ s * (w.re - min z.re w.re) :=
    mul_nonneg hs.1 (sub_nonneg.mpr hwmin)
  nlinarith
end CohnElkies
