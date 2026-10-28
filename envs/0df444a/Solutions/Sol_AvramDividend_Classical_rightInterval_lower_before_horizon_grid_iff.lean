-- Prove2me | solution 1 for AvramDividend.Classical.rightInterval_lower_before_horizon_grid_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:04:39.82502+00:00
-- url     : https://prove2.me/submissions/d20eeccb-6c18-47f5-a297-49555664dfc9

import Mathlib.Data.NNReal.Defs
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
open AvramDividend.Classical

/-! Deterministic finite-horizon strict lower crossing on the rational grid. -/
theorem solution
    (g : ℝ≥0 → ℝ) (lower : ℝ)
    (hRight : ∀ s : ℝ≥0, g s < lower →
      ∃ u : ℝ≥0, s < u ∧
        ∀ r : ℝ≥0, s ≤ r → r < u → g r < lower)
    (T : ℝ≥0) :
    (∃ s : ℝ≥0, s < T ∧ g s < lower) ↔
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T ∧
        g ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) < lower := by
  constructor
  · rintro ⟨s, hsT, hsExit⟩
    obtain ⟨u, hsu, hright⟩ := hRight s hsExit
    have hmin : s < min u T := lt_min hsu hsT
    have hδ : 0 < min u T - s := tsub_pos_iff_lt.mpr hmin
    obtain ⟨n, hn, hnlt⟩ := NNReal.exists_nat_pos_inv_lt hδ
    let h : ℝ≥0 := (n : ℝ≥0)⁻¹
    have hh : 0 < h := inv_pos.mpr (by exact_mod_cast hn)
    obtain ⟨hlo, hhi⟩ := chat03_nnreal_grid_ceiling_bracket s h hh
    have hLess : s + h < min u T := by
      calc
        s + h < s + (min u T - s) :=
          by simpa only [h] using add_lt_add_right hnlt s
        _ = min u T := add_tsub_cancel_of_le hmin.le
    let k : ℕ := Nat.ceil (s / h)
    refine ⟨n, hn, k, ?_, ?_⟩
    · exact hhi.trans (hLess.trans_le (min_le_right _ _))
    · exact hright _ hlo (hhi.trans (hLess.trans_le (min_le_left _ _)))
  · rintro ⟨n, _, k, hT, hExit⟩
    exact ⟨(k : ℝ≥0) * (n : ℝ≥0)⁻¹, hT, hExit⟩
