-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_allcap_full_predictable_compact_bands
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:58:34.487192+00:00
-- url     : https://prove2.me/submissions/da51c137-dd8e-4608-a408-8d5c7f9e3995

import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_uncapped_full_predictable_compact_bands
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_finite_full_predictable_compact_bands
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- For every positive cap, the original full predictable pre-reserve mask
bands [a_n,b_n] exhaust the strict interior and have a compact buffer. -/
theorem solution (C : ℝ≥0∞) (hC : 0 < C) :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) := by
  by_cases hTop : C = ⊤
  · subst C
    obtain ⟨a, b, ha, ha2, hab, hBand, hEvent⟩ :=
      avram_bv_meas7_uncapped_full_predictable_compact_bands
    refine ⟨a, b, ha, ha2, hab, hBand, ?_⟩
    intro y hy _
    exact hEvent y hy
  · exact avram_bv_meas7_finite_full_predictable_compact_bands C hC hTop
