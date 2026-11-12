-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite72_cap_gap_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:33:46.351385+00:00
-- url     : https://prove2.me/submissions/0340da21-30a3-4bb2-9033-c2f3dc166fab

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- The upper-cap corner defect is nonnegative when the excess-value
    function `w - id` is monotone along the cap interval. -/
theorem solution
    (w : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hmono : MonotoneOn (fun z : ℝ => w z - z) (Icc a b)) :
    0 ≤ (w b - w a) - (b - a) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have h : w a - a ≤ w b - b := hmono ha hb hab
  linarith
