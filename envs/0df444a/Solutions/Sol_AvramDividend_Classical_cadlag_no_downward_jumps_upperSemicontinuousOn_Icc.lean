-- Prove2me | solution 1 for AvramDividend.Classical.cadlag_no_downward_jumps_upperSemicontinuousOn_Icc
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:12:01.445506+00:00
-- url     : https://prove2.me/submissions/16530150-2c2e-4dba-bebc-07111b12b027

import Mathlib
open Filter Set Topology
open scoped NNReal

theorem solution
    (f : ℝ≥0 → ℝ) (ζ : ℝ≥0)
    (hRight : ∀ t : ℝ≥0, ContinuousWithinAt f (Ici t) t)
    (hLeft : ∀ t : ℝ≥0, 0 < t →
      ∃ l : ℝ, Filter.Tendsto f
        (nhdsWithin t (Iio t)) (nhds l))
    (hNoDown : ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Filter.Tendsto f (nhdsWithin t (Iio t)) (nhds l) →
      l ≤ f t) :
    UpperSemicontinuousOn f (Icc 0 ζ) := by
  intro t _
  refine UpperSemicontinuousAt.upperSemicontinuousWithinAt (s := Icc 0 ζ) (x := t) ?_
  intro y hy
  have hR : ∀ᶠ x in 𝓝[≥] t, f x < y := (hRight t).eventually (gt_mem_nhds hy)
  have hL : ∀ᶠ x in 𝓝[<] t, f x < y := by
    rcases eq_or_lt_of_le (zero_le (a := t)) with h0 | hpos
    · subst h0
      have : Iio (0 : ℝ≥0) = ∅ := by ext x; simp
      rw [this, nhdsWithin_empty]; exact Filter.eventually_bot
    · obtain ⟨l, hl⟩ := hLeft t hpos
      exact hl.eventually (gt_mem_nhds (lt_of_le_of_lt (hNoDown t l hpos hl) hy))
  rw [← nhdsLT_sup_nhdsGE]
  exact Filter.eventually_sup.2 ⟨hL, hR⟩
