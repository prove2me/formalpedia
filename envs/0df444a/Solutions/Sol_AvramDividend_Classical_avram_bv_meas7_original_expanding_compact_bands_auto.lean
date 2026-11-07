-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_original_expanding_compact_bands_auto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:21:56.159667+00:00
-- url     : https://prove2.me/submissions/522b9726-ffd4-4598-8351-1ebfd5418aa1

import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_expanding_compact_bands
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_uncapped_expanding_compact_band
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- Every positive original dividend cap, including infinity, admits the
compact pre-reserve bands required by the physical compensated source. -/
theorem solution (C : ℝ≥0∞) (hC : 0 < C) :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) := by
  by_cases hTop : C = ⊤
  · subst C
    refine ⟨(fun n => 1 / ((n : ℝ) + 1)), (fun n => (n : ℝ) + 2), ?_, ?_, ?_, ?_⟩
    · intro n
      exact (avram_p3_grid4_uncapped_expanding_compact_band n).1
    · intro n
      exact (avram_p3_grid4_uncapped_expanding_compact_band n).2.1
    · intro n
      exact (avram_p3_grid4_uncapped_expanding_compact_band n).2.2.1
    · intro n
      exact (avram_p3_grid4_uncapped_expanding_compact_band n).2.2.2
  · exact avram_p3_grid4_finite_cap_expanding_compact_bands C hC hTop
