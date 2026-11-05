-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_each_strict_cap_point_has_compact_C1_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:30:46.89347+00:00
-- url     : https://prove2.me/submissions/9bda1c84-14ce-45df-ae16-5e8bd4262bb4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Any actual positive reserve below the cap admits a physical compact
interior strip, uniformly covering finite and infinite cap alternatives. -/
theorem solution (C : ℝ≥0∞) (y : ℝ)
    (hy : 0 < y) (hyC : ENNReal.ofReal y < C) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ 2 ∧ a ≤ b ∧ y ∈ Icc a b ∧
      Icc (a / 2) b ⊆
        {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C} := by
  let a : ℝ := min 1 (y / 2)
  have ha : 0 < a := by
    dsimp [a]
    apply lt_min
    · norm_num
    · linarith
  have ha2 : a ≤ 2 :=
    (min_le_left (1 : ℝ) (y / 2)).trans (by norm_num)
  have hay : a ≤ y :=
    (min_le_right (1 : ℝ) (y / 2)).trans (by linarith)
  refine ⟨a, y, ha, ha2, hay, ⟨hay, le_rfl⟩, ?_⟩
  intro v hv
  have hvpos : 0 < v := lt_of_lt_of_le (half_pos ha) hv.1
  have hvc : ENNReal.ofReal v ≤ ENNReal.ofReal y :=
    ENNReal.ofReal_le_ofReal hv.2
  exact ⟨hvpos, hvc.trans_lt hyC⟩
