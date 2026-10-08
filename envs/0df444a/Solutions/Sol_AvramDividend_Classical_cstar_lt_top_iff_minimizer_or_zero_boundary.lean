-- Prove2me | solution 1 for AvramDividend.Classical.cstar_lt_top_iff_minimizer_or_zero_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T15:29:30.180125+00:00
-- url     : https://prove2.me/submissions/48775cd9-783f-4d1d-8e75-f6bc7d13ec2e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_of_minimizer

open AvramDividend.Classical
open scoped ENNReal

theorem solution (W : ℝ → ℝ) :
    cstar W < ⊤ ↔
      (cstarSet W).Nonempty ∨
        ∀ x : ℝ, 0 < x →
          derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal) := by
  classical
  constructor
  · intro hfin
    by_cases hmin : (cstarSet W).Nonempty
    · exact Or.inl hmin
    · right
      by_contra hn
      have htop : cstar W = (⊤ : ℝ≥0∞) := by
        simp [cstar, hmin, hn]
      rw [htop] at hfin
      exact (lt_irrefl (⊤ : ℝ≥0∞)) hfin
  · intro h
    rcases h with hmin | hzero
    · exact cstar_lt_top_of_minimizer W hmin
    · by_cases hmin : (cstarSet W).Nonempty
      · exact cstar_lt_top_of_minimizer W hmin
      · unfold cstar
        rw [if_neg hmin, if_pos hzero]
        simp
