-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_uncapped_expanding_compact_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:16:53.846618+00:00
-- url     : https://prove2.me/submissions/3fd9f1bc-7e9d-4ee6-a06f-9dad358e4da5

import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped ENNReal
noncomputable section

/-- Explicit compact interior bands expanding through the uncapped half-line. -/
theorem solution (n : ℕ) :
    0 < (1 : ℝ) / ((n : ℝ) + 1) ∧
    (1 : ℝ) / ((n : ℝ) + 1) ≤ 2 ∧
    (1 : ℝ) / ((n : ℝ) + 1) ≤ ((n : ℝ) + 2) ∧
    Icc (((1 : ℝ) / ((n : ℝ) + 1)) / 2) ((n : ℝ) + 2) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)} := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  have hle : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    apply (div_le_iff₀ hn).2
    linarith
  refine ⟨hpos, le_trans hle (by norm_num), ?_, ?_⟩
  · linarith
  · intro y hy
    rcases hy with ⟨hyl, _⟩
    change 0 < y ∧ ENNReal.ofReal y < ⊤
    constructor
    · have : 0 < (1 : ℝ) / ((n : ℝ) + 1) / 2 := by positivity
      exact lt_of_lt_of_le this hyl
    · exact ENNReal.ofReal_lt_top
