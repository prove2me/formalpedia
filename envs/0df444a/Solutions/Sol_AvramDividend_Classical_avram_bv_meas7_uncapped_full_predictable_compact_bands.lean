-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_uncapped_full_predictable_compact_bands
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:54:19.597863+00:00
-- url     : https://prove2.me/submissions/a71ec308-3687-4b9b-ab12-2f0ad6f54dc2

import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_uncapped_expanding_compact_band
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_uncapped_full_predictable_band_eventually_contains_reserve
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- The original uncapped predictable full pre-reserve bands E_n=[a_n,b_n]
are compact and exhaust every positive reserve, with no half-band gap. -/
theorem solution :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)}) ∧
      (∀ y : ℝ, 0 < y → ∃ N : ℕ, ∀ n ≥ N,
        y ∈ Icc (a n) (b n)) := by
  refine ⟨(fun n => 1 / ((n : ℝ) + 1)), (fun n => (n : ℝ) + 2),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (avram_p3_grid4_uncapped_expanding_compact_band n).1
  · intro n
    exact (avram_p3_grid4_uncapped_expanding_compact_band n).2.1
  · intro n
    exact (avram_p3_grid4_uncapped_expanding_compact_band n).2.2.1
  · intro n
    exact (avram_p3_grid4_uncapped_expanding_compact_band n).2.2.2
  · intro y hy
    exact avram_bv_meas7_uncapped_full_predictable_band_eventually_contains_reserve y hy
