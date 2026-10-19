-- Prove2me | solution 2 for CohnElkies.complexFrullaniSegment_min_re_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:13:53.044647+00:00
-- url     : https://prove2.me/submissions/82904a45-3b15-4357-bfc3-c78fc6846530

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


theorem solution
    (z w : ℂ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    min z.re w.re ≤ (complexFrullaniSegment z w s).re := by
  unfold complexFrullaniSegment
  obtain ⟨hs0, hs1⟩ := hs
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.sub_im, zero_mul, sub_zero]
  have h1 : (1 - s) * min z.re w.re ≤ (1 - s) * z.re :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith)
  have h2 : s * min z.re w.re ≤ s * w.re :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) hs0
  nlinarith

