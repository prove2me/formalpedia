-- Prove2me | solution 2 for CohnElkies.complexFrullaniSegment_re_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:24:14.37181+00:00
-- url     : https://prove2.me/submissions/dac44a38-b38b-453e-b80f-af7ff58f88bd

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


theorem solution {z w : ℂ}
    (hz : 0 < z.re) (hw : 0 < w.re)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    0 < (complexFrullaniSegment z w s).re := by
  unfold complexFrullaniSegment
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im, zero_mul, sub_zero]
  have h0 := hs.1; have h1 := hs.2
  rcases h1.lt_or_eq with h | h
  · nlinarith [mul_pos (sub_pos.2 h) hz, mul_nonneg h0 hw.le]
  · subst h; linarith

