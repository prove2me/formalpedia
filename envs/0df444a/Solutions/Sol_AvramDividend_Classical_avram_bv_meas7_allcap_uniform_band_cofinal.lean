-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_allcap_uniform_band_cofinal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:42:00.050389+00:00
-- url     : https://prove2.me/submissions/368a130e-e8b2-407c-a24e-9f579006f511

import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_uncapped_uniform_band_cofinal
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_finite_cap_uniform_band_cofinal
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- For every positive original dividend cap, including infinity, choose
compact reserve bands that eventually cover every strict interior reserve. -/
theorem solution (C : ℝ≥0∞) (hC : 0 < C) :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n / 2) (b n)) := by
  by_cases hTop : C = ⊤
  · subst C
    obtain ⟨a, b, ha, ha2, hab, hBand, hEvent⟩ :=
      avram_bv_meas7_uncapped_uniform_band_cofinal
    refine ⟨a, b, ha, ha2, hab, hBand, ?_⟩
    intro y hy _
    exact hEvent y hy
  · exact avram_bv_meas7_finite_cap_uniform_band_cofinal C hC hTop
