-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_strict_cap_rational_compact_strips_countable_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:14:01.211533+00:00
-- url     : https://prove2.me/submissions/12f0e5a9-42db-4f7f-bb38-4b52e4406633

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every positive strict-cap reserve point admits a rational compact band,
giving a countable deterministic family for predictable exhaustion. -/
theorem solution (C : ℝ≥0∞) (y : ℝ)
    (hy : 0 < y) (hyC : ENNReal.ofReal y < C) :
    ∃ a b : ℚ,
      0 < (a : ℝ) ∧ (a : ℝ) ≤ 2 ∧
      (a : ℝ) ≤ (b : ℝ) ∧
      y ∈ Ioo (a : ℝ) (b : ℝ) ∧
      Icc ((a : ℝ) / 2) (b : ℝ) ⊆
        {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C} := by
  have hmin : (0 : ℝ) < min 1 y := by
    apply lt_min
    · norm_num
    · exact hy
  obtain ⟨a, ha0, ha1⟩ := exists_rat_btwn hmin
  have haY : (a : ℝ) < y :=
    ha1.trans_le (min_le_right (1 : ℝ) y)
  have ha2 : (a : ℝ) ≤ 2 := by
    have ha1' : (a : ℝ) ≤ 1 :=
      (le_of_lt ha1).trans (min_le_left (1 : ℝ) y)
    linarith
  have hbExists : ∃ b : ℚ,
      y < (b : ℝ) ∧ ENNReal.ofReal (b : ℝ) < C := by
    by_cases hTop : C = ⊤
    · obtain ⟨b, hyb, _⟩ := exists_rat_btwn
        (show y < y + 1 by linarith)
      exact ⟨b, hyb, by simp [hTop]⟩
    · have hyReal : y < C.toReal :=
        (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy) hTop).mp hyC
      obtain ⟨b, hyb, hbC⟩ := exists_rat_btwn hyReal
      have hb0 : 0 ≤ (b : ℝ) := le_of_lt (hy.trans hyb)
      exact ⟨b, hyb,
        (ENNReal.ofReal_lt_iff_lt_toReal hb0 hTop).mpr hbC⟩
  obtain ⟨b, hyb, hbC⟩ := hbExists
  have hab : (a : ℝ) ≤ (b : ℝ) := le_of_lt (haY.trans hyb)
  refine ⟨a, b, ha0, ha2, hab, ⟨haY, hyb⟩, ?_⟩
  intro v hv
  have hvpos : 0 < v := lt_of_lt_of_le (half_pos ha0) hv.1
  have hvc : ENNReal.ofReal v ≤ ENNReal.ofReal (b : ℝ) :=
    ENNReal.ofReal_le_ofReal hv.2
  exact ⟨hvpos, hvc.trans_lt hbC⟩
