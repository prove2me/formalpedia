-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_allcap_expanding_compact_band_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:35:59.378851+00:00
-- url     : https://prove2.me/submissions/e5ec0d2d-cb2c-49f3-8636-32926627f4fe

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_uncapped_expanding_compact_band
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_expanding_compact_bands
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped ENNReal
noncomputable section

/-- An actual compact localisation family for every strictly positive dividend cap. -/
theorem solution (C : ℝ≥0∞) (hC : 0 < C) :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) := by
  by_cases hTop : C = ⊤
  · subst C
    let a : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    let b : ℕ → ℝ := fun n => (n : ℝ) + 2
    refine ⟨a, b, ?_, ?_, ?_, ?_⟩
    · intro n
      exact (AvramDividend.Classical.avram_p3_grid4_uncapped_expanding_compact_band n).1
    · intro n
      exact (AvramDividend.Classical.avram_p3_grid4_uncapped_expanding_compact_band n).2.1
    · intro n
      exact (AvramDividend.Classical.avram_p3_grid4_uncapped_expanding_compact_band n).2.2.1
    · intro n
      exact (AvramDividend.Classical.avram_p3_grid4_uncapped_expanding_compact_band n).2.2.2
  · exact AvramDividend.Classical.avram_p3_grid4_finite_cap_expanding_compact_bands C hC hTop
