-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_abovecap_corrected_parenthesised_grid_defect_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:04:15.077959+00:00
-- url     : https://prove2.me/submissions/9c1c4220-9068-43f2-89e2-d7b56f432405

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    (m : ℕ) (hm : 0 < m) :
    let w : ℝ → ℝ := fun y =>
      if y < 0 then 0 else if y ≤ 1 then y else 2 - y
    let V : ℝ → ℝ := fun y =>
      if y ≤ 1 then w y else w 1 + (y - 1)
    (∑ _i ∈ Finset.range m,
      (V (1 + 1 / (m : ℝ)) - w (1 + 1 / (m : ℝ)))) = 2 := by
  have hmp : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmp
  let w : ℝ → ℝ := fun z =>
    if z < 0 then 0 else if z ≤ 1 then z else 2 - z
  let V : ℝ → ℝ := fun z =>
    if z ≤ 1 then w z else w 1 + (z - 1)
  let y : ℝ := 1 + 1 / (m : ℝ)
  change (∑ _i ∈ Finset.range m, (V y - w y)) = 2
  have hfrac : (0 : ℝ) < 1 / (m : ℝ) := div_pos one_pos hmp
  have hgt : (1 : ℝ) < y := by dsimp [y]; linarith
  have hnn : ¬ y < 0 := by linarith
  have hnle : ¬ y ≤ 1 := not_le.mpr hgt
  have hw1 : w 1 = 1 := by norm_num [w]
  have hwy : w y = 2 - y := by simp only [w, hnn, hnle, if_false]
  have hVy : V y = y := by
    simp only [V, hnle, if_false, hw1]
    ring
  have hterm : V y - w y = 2 / (m : ℝ) := by
    rw [hVy, hwy]
    dsimp [y]
    ring
  simp only [hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp [hmne]
