-- Prove2me | solution 1 for CohnElkies.complexFrullaniSegment_re_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/0f9578a1-b802-4d12-a5cd-be8e34ac2af3

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
theorem _root_.solution {z w : ℂ}
    (hz : 0 < z.re) (hw : 0 < w.re)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    0 < (complexFrullaniSegment z w s).re := by
  simp only [complexFrullaniSegment, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, zero_mul, sub_zero]
  by_cases hzero : s = 0
  · simpa [hzero] using! hz
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hzero)
    have hfirst : 0 ≤ (1 - s) * z.re :=
      mul_nonneg (sub_nonneg.mpr hs.2) hz.le
    have hsecond : 0 < s * w.re := mul_pos hspos hw
    nlinarith
end CohnElkies
