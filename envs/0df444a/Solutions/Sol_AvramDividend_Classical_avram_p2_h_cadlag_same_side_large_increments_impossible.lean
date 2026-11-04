-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_same_side_large_increments_impossible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:28:15.894066+00:00
-- url     : https://prove2.me/submissions/845d3bd0-c9df-4e51-ad0a-a0de9e607300

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_same_side_shrinking_increments_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

/-- A positive lower bound on shrinking increments excludes both
noncrossing positional cases at the limiting time. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (t : ℝ≥0) (a b : ℕ → ℝ≥0)
    (hL : Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ContinuousWithinAt Y (Ici t) t)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hlarge : ∀ n : ℕ, ρ ≤ |Y (b n) - Y (a n)|)
    (hsides :
      (Tendsto a atTop (𝓝[<] t) ∧ Tendsto b atTop (𝓝[<] t)) ∨
      (Tendsto a atTop (nhdsWithin t (Ici t)) ∧
        Tendsto b atTop (nhdsWithin t (Ici t)))) :
    False := by
  have he : ∀ᶠ n in (atTop : Filter ℕ),
      ρ ≤ |Y (b n) - Y (a n)| :=
    Filter.Eventually.of_forall hlarge
  rcases hsides with hleft | hright
  · have hz := (avram_p2_h_cadlag_same_side_shrinking_increments_zero
      Y t a b hL hR).1 hleft
    have hn : ρ ≤ |(0 : ℝ)| := ge_of_tendsto hz.abs he
    exact (not_le_of_gt hρ) (by simpa using hn)
  · have hz := (avram_p2_h_cadlag_same_side_shrinking_increments_zero
      Y t a b hL hR).2 hright
    have hn : ρ ≤ |(0 : ℝ)| := ge_of_tendsto hz.abs he
    exact (not_le_of_gt hρ) (by simpa using hn)
