-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_tail11_singular_cell_outside_any_positive_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T11:15:10.835738+00:00
-- url     : https://prove2.me/submissions/c9ca2550-daf8-4de2-b7fb-9becb48e4d6c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail11_singular_uniform_neighbourhood_unbounded_below

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

/-- Every positive compact-band edge misses a sufficiently small reserve whose
signed physical generator cell is arbitrarily negative. -/
theorem solution (K : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ t : ℝ,
      0 < t ∧ t < a / 2 ∧
      t ≤ (1 / ((K : ℝ) + 4)) ^ 2 ∧
      (1 / ((K : ℝ) + 4)) *
        (3 + t ^ 2 - 4 * t - 2 / t) ≤ -(K : ℝ) := by
  let h : ℝ := 1 / ((K : ℝ) + 4)
  have hh : 0 < h := by
    dsimp [h]
    positivity
  let t : ℝ := min (a / 4) (h ^ 2 / 2)
  have ht0 : 0 < t := by
    change 0 < min (a / 4) (h ^ 2 / 2)
    exact lt_min (by positivity) (by positivity)
  have hleft : t ≤ a / 4 := by
    change min (a / 4) (h ^ 2 / 2) ≤ a / 4
    exact min_le_left _ _
  have hright : t ≤ h ^ 2 / 2 := by
    change min (a / 4) (h ^ 2 / 2) ≤ h ^ 2 / 2
    exact min_le_right _ _
  have htband : t < a / 2 := by linarith
  have htsq : t ≤ h ^ 2 := by nlinarith [sq_nonneg h]
  refine ⟨t, ht0, htband, ?_, ?_⟩
  · simpa [h] using htsq
  · exact avram_bv_tail11_singular_uniform_neighbourhood_unbounded_below
      K t ht0 (by simpa [h] using htsq)
