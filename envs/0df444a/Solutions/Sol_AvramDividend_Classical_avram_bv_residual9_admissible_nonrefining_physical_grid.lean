-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_admissible_nonrefining_physical_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:26:41.851483+00:00
-- url     : https://prove2.me/submissions/0694ad92-c199-44da-8c30-df2755543695

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original endpoint and monotonicity conditions permit a macroscopic first cell. -/
theorem solution :
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n : ℕ, u n 0 = 0 ∧
        ((u n (n + 1) : ℝ) = 1 - 1 / ((n : ℝ) + 2))) ∧
      (∀ (n i : ℕ), i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n : ℕ, (1 / 2 : ℝ) ≤ (u n 1 : ℝ)) := by
  let v : ℕ → ℝ≥0 := fun n => ⟨((n : ℝ) + 1) / ((n : ℝ) + 2), by positivity⟩
  let u : ℕ → ℕ → ℝ≥0 := fun n i => if i = 0 then 0 else v n
  refine ⟨u, ?_, ?_, ?_⟩
  · intro n
    constructor
    · simp [u]
    · have hn : n + 1 ≠ 0 := by omega
      simp only [u, hn, ↓reduceIte]
      change ((n : ℝ) + 1) / ((n : ℝ) + 2) =
        1 - 1 / ((n : ℝ) + 2)
      have hd : ((n : ℝ) + 2) ≠ 0 := by positivity
      field_simp
      ring
  · intro n i hi
    by_cases hi0 : i = 0
    · subst i
      simp [u]
    · have hs : i + 1 ≠ 0 := by omega
      simp [u, hi0, hs]
  · intro n
    simp only [u, show (1 : ℕ) ≠ 0 by omega, ↓reduceIte]
    change (1 / 2 : ℝ) ≤ ((n : ℝ) + 1) / ((n : ℝ) + 2)
    have hd : 0 < ((n : ℝ) + 2) := by positivity
    apply (le_div_iff₀ hd).2
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    nlinarith
