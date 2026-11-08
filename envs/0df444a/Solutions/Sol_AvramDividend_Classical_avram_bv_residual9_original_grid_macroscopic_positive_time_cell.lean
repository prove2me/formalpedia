-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_original_grid_macroscopic_positive_time_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:56:50.987791+00:00
-- url     : https://prove2.me/submissions/b1beb780-9a82-4958-8256-365bcfd7f1f3

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_monotone_grid_nonuniform_counterexample
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (T : ℝ) (hT : 0 < T) :
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n, u n 0 = 0 ∧
        ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2))) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n, 1 ≤ n →
        0 < (u n 1 : ℝ) ∧
        T / 4 ≤ (u n 2 : ℝ) - (u n 1 : ℝ)) := by
  classical
  obtain ⟨u, hu_grid, hu_mono, hu_tail, hu_nonuniform⟩ :=
    avram_bv_residual9_monotone_grid_nonuniform_counterexample T hT
  let v : ℕ → ℕ → ℝ≥0 := fun n i =>
    if n = 0 then u n i else
    if i = 0 then 0 else
    if i = 1 then u n (n + 1) / 2 else u n (n + 1)
  refine ⟨v, ?_, ?_, ?_⟩
  · intro n
    constructor
    · by_cases hn : n = 0
      · subst n
        simpa [v] using (hu_grid 0).1
      · simp [v, hn]
    · by_cases hn : n = 0
      · subst n
        simpa [v] using (hu_grid 0).2
      · have hne0 : n + 1 ≠ 0 := by omega
        have hne1 : n + 1 ≠ 1 := by omega
        simpa [v, hn, hne0, hne1] using (hu_grid n).2
  · intro n i hi
    by_cases hn : n = 0
    · simpa [v, hn] using hu_mono n i hi
    · by_cases hi0 : i = 0
      · subst i
        simp [v, hn]
      · by_cases hi1 : i = 1
        · subst i
          have hhalf : u n (n + 1) / (2 : ℝ≥0) ≤ u n (n + 1) := by
            apply div_le_self
            · exact zero_le
            · norm_num
          simpa [v, hn] using hhalf
        · have hi0' : i + 1 ≠ 0 := by omega
          have hi1' : i + 1 ≠ 1 := by omega
          simp [v, hn, hi0, hi1, hi0', hi1']
  · intro n hn
    have hne : n ≠ 0 := by omega
    have hden : 0 < (n : ℝ) + 2 := by positivity
    have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hquarter : T / ((n : ℝ) + 2) ≤ T / 2 := by
      apply (div_le_iff₀ hden).2
      nlinarith [mul_nonneg (le_of_lt hT) hnnonneg]
    have hE : T / 2 ≤ (u n (n + 1) : ℝ) := by
      rw [(hu_grid n).2]
      linarith
    have hEpos : 0 < (u n (n + 1) : ℝ) := by linarith
    have hv1 : v n 1 = u n (n + 1) / 2 := by simp [v, hne]
    have hv2 : v n 2 = u n (n + 1) := by simp [v, hne]
    constructor
    · rw [hv1]
      exact_mod_cast (div_pos (show (0 : ℝ≥0) < u n (n + 1) by
        exact_mod_cast hEpos) (by norm_num : (0 : ℝ≥0) < 2))
    · rw [hv1, hv2]
      norm_num at *
      linarith
