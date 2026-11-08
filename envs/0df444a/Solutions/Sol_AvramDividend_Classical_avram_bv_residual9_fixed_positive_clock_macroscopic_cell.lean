-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_fixed_positive_clock_macroscopic_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:05:29.912535+00:00
-- url     : https://prove2.me/submissions/da8175e1-1cee-448b-94bf-ed931b3e1fa0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_monotone_grid_nonuniform_counterexample
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A prescribed positive observation clock can precede a persistent large cell. -/
theorem solution
    (T a : ℝ) (hT : 0 < T) (ha : 0 < a) (haT : a ≤ T / 4) :
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n, u n 0 = 0 ∧
        ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2))) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n, 1 ≤ n →
        (u n 1 : ℝ) = a ∧
        T / 4 ≤ (u n 2 : ℝ) - (u n 1 : ℝ)) := by
  classical
  obtain ⟨u, hu_grid, hu_mono, hu_tail, hu_nonuniform⟩ :=
    avram_bv_residual9_monotone_grid_nonuniform_counterexample T hT
  let aNN : ℝ≥0 := ⟨a, le_of_lt ha⟩
  have hend : ∀ n, T / 2 ≤ (u n (n + 1) : ℝ) := by
    intro n
    have hden : 0 < (n : ℝ) + 2 := by positivity
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hdelta : T / ((n : ℝ) + 2) ≤ T / 2 := by
      apply (div_le_iff₀ hden).2
      nlinarith [mul_nonneg (le_of_lt hT) hn]
    rw [(hu_grid n).2]
    linarith
  have ha_le_end : ∀ n, aNN ≤ u n (n + 1) := by
    intro n
    apply NNReal.coe_le_coe.mp
    change a ≤ (u n (n + 1) : ℝ)
    linarith [hend n, haT]
  let v : ℕ → ℕ → ℝ≥0 := fun n i =>
    if n = 0 then u n i else
    if i = 0 then 0 else
    if i = 1 then aNN else u n (n + 1)
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
          simpa [v, hn] using ha_le_end n
        · have hi0' : i + 1 ≠ 0 := by omega
          have hi1' : i + 1 ≠ 1 := by omega
          simp [v, hn, hi0, hi1, hi0', hi1']
  · intro n hn
    have hne : n ≠ 0 := by omega
    have hv1 : v n 1 = aNN := by simp [v, hne]
    have hv2 : v n 2 = u n (n + 1) := by simp [v, hne]
    constructor
    · rw [hv1]
      rfl
    · rw [hv1, hv2]
      change T / 4 ≤ (u n (n + 1) : ℝ) - a
      linarith [hend n, haT]
