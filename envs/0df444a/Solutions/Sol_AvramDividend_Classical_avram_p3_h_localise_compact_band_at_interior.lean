-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_h_localise_compact_band_at_interior
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:58:37.160067+00:00
-- url     : https://prove2.me/submissions/7313ce07-4b60-4cdb-ab70-0b2012f8506b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every positive point under the reserve cap lies in a compact interval
which stays strictly inside the positive-cap region and has a controlled
lower endpoint. This supplies the exact a, b localisation premises used
by the source-specific stopped BV jump compensator. -/
theorem solution
    (C : ℝ≥0∞) (z : ℝ)
    (hz : 0 < z) (hzC : ENNReal.ofReal z < C) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ 2 ∧ a ≤ b ∧ z ∈ Icc a b ∧
      Icc (a / 2) b ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
  let a : ℝ := min (z / 2) 1
  have ha : 0 < a := by
    dsimp [a]
    exact lt_min (by linarith) (by norm_num)
  have ha2 : a ≤ 2 := by
    have h := min_le_right (z / 2) (1 : ℝ)
    dsimp [a]
    linarith
  have haz : a ≤ z := by
    have h := min_le_left (z / 2) (1 : ℝ)
    dsimp [a]
    linarith
  refine ⟨a, z, ha, ha2, haz, ⟨haz, le_rfl⟩, ?_⟩
  intro y hy
  change 0 < y ∧ ENNReal.ofReal y < C
  constructor
  · have ha' : 0 < a / 2 := half_pos ha
    exact lt_of_lt_of_le ha' hy.1
  · exact lt_of_le_of_lt (ENNReal.ofReal_mono hy.2) hzC
