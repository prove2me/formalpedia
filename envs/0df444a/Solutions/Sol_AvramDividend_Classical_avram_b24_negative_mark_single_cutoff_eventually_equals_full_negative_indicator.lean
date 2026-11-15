-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_negative_mark_single_cutoff_eventually_equals_full_negative_indicator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:01:38.513363+00:00
-- url     : https://prove2.me/submissions/8afc226f-e069-4823-9e49-e55e9692730c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    (z : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      (if -1 < z ∧ z ≤ -(1 / ((n : ℝ) + 1)) then z else 0) =
      (if -1 < z ∧ z < 0 then z else 0) := by
  by_cases hLo : -1 < z
  · by_cases hNeg : z < 0
    · have hp : (0 : ℝ) < -z := neg_pos.mpr hNeg
      have hEv : ∀ᶠ n : ℕ in atTop, (1 / ((n : ℝ) + 1)) < -z :=
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
          (isOpen_Iio.mem_nhds hp)
      filter_upwards [hEv] with n hn
      have hCut : z ≤ -(1 / ((n : ℝ) + 1)) := by linarith
      have hL : -1 < z ∧ z ≤ -(1 / ((n : ℝ) + 1)) := ⟨hLo, hCut⟩
      have hR : -1 < z ∧ z < 0 := ⟨hLo, hNeg⟩
      simp only [if_pos hL, if_pos hR]
    · filter_upwards [] with n
      have hDen : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hCutNeg : -(1 / ((n : ℝ) + 1)) < 0 :=
        neg_lt_zero.mpr (div_pos (by norm_num) hDen)
      have hNo : ¬ z ≤ -(1 / ((n : ℝ) + 1)) := by
        intro hCut
        exact hNeg (lt_of_le_of_lt hCut hCutNeg)
      have hL : ¬ (-1 < z ∧ z ≤ -(1 / ((n : ℝ) + 1))) :=
        fun h => hNo h.2
      have hR : ¬ (-1 < z ∧ z < 0) := fun h => hNeg h.2
      simp only [if_neg hL, if_neg hR]
  · filter_upwards [] with n
    have hL : ¬ (-1 < z ∧ z ≤ -(1 / ((n : ℝ) + 1))) :=
      fun h => hLo h.1
    have hR : ¬ (-1 < z ∧ z < 0) := fun h => hLo h.1
    simp only [if_neg hL, if_neg hR]
