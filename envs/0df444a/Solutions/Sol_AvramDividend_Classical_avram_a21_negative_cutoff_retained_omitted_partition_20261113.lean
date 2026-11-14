-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_negative_cutoff_retained_omitted_partition_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:50:22.116187+00:00
-- url     : https://prove2.me/submissions/8eae4df1-e138-40c3-bf5c-6e95510e6e48

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
noncomputable section

/-- The physically retained negative jump strip and the omitted near-zero
tail partition the full small-jump interval with exact endpoint ownership. -/
theorem solution
    (n : ℕ) :
    Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))) ∪
      Ioo (-(1 / ((n : ℝ) + 1))) 0 = Ioo (-1 : ℝ) 0 := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hfrac : 1 / ((n : ℝ) + 1) ≤ 1 := by
    apply (div_le_iff₀ hn).mpr
    linarith
  have hlow : (-1 : ℝ) ≤ -(1 / ((n : ℝ) + 1)) := by linarith
  have hhigh : -(1 / ((n : ℝ) + 1)) < 0 := by
    have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  exact Set.Ioc_union_Ioo_eq_Ioo hlow hhigh
