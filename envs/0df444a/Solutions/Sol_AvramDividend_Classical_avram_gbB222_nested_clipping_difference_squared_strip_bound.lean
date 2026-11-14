-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB222_nested_clipping_difference_squared_strip_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:56:39.688208+00:00
-- url     : https://prove2.me/submissions/bbf9eccb-f335-433d-977a-e41bb234915c

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
import Theorems.Thm_AvramDividend_Classical_avram_gbB221_clipped_gradients_agree_off_nested_cutoff_strips
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

/-- Squared clipped-gradient error is bounded by boundary-strip occupancy. -/
theorem solution
    (w : ℝ → ℝ) (a a' b' b B : ℝ)
    (ha : a ≤ a') (hab : a' ≤ b') (hb : b' ≤ b)
    (hB : 1 ≤ B)
    (hgrad : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ B)
    (y : ℝ) :
    ((if y ∈ Set.Icc a b then deriv w y else 1) -
      (if y ∈ Set.Icc a' b' then deriv w y else 1))^2 ≤
      4 * B^2 *
        (if y ∈ Set.Icc a a' ∨ y ∈ Set.Icc b' b then (1 : ℝ) else 0) := by
  let co : ℝ := if y ∈ Set.Icc a b then deriv w y else 1
  let cn : ℝ := if y ∈ Set.Icc a' b' then deriv w y else 1
  have hClip :=
    avram_gbB221_clipped_gradients_agree_off_nested_cutoff_strips
      w a a' b' b B ha hab hb hB hgrad y
  by_cases hs : y ∈ Set.Icc a a' ∨ y ∈ Set.Icc b' b
  · have hAbs : |co - cn| ≤ 2 * B := by
      simpa only [co, cn] using hClip.2
    have hLo : -(2 * B) ≤ co - cn := (abs_le.mp hAbs).1
    have hHi : co - cn ≤ 2 * B := (abs_le.mp hAbs).2
    have hm : 0 ≤ (2 * B - (co - cn)) * (2 * B + (co - cn)) :=
      mul_nonneg (by linarith) (by linarith)
    simp only [if_pos hs, mul_one]
    change (co - cn)^2 ≤ 4 * B^2
    nlinarith
  · have hEq : co = cn := by
      simpa only [co, cn] using
        (hClip.1 (fun hh => hs (Or.inl hh))
          (fun hh => hs (Or.inr hh)))
    simp only [if_neg hs, mul_zero]
    change (co - cn)^2 ≤ 0
    rw [hEq]
    norm_num

