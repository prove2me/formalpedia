-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_C1_positive_cap_compact_band_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:44:00.24921+00:00
-- url     : https://prove2.me/submissions/2474e046-7e25-4505-a9b8-fd9879a8005b

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal

/-- Smoothness on the genuinely positive interior below the cap supplies
a BV first-moment Lipschitz bound on each compact interior reserve band. -/
theorem solution (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a)
    (hab : a ≤ b) (hb : ENNReal.ofReal b < C) :
    ∃ K : ℝ≥0, LipschitzOnWith K w (Icc a b) := by
  have hsub : Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy
    rcases mem_Icc.mp hy with ⟨hya, hyb⟩
    exact ⟨lt_of_lt_of_le ha hya,
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hyb) hb⟩
  have hw' : ContDiffOn ℝ 1 w (Icc a b) := hw.mono hsub
  exact hw'.exists_lipschitzOnWith
    (by norm_num) (convex_Icc a b) isCompact_Icc
