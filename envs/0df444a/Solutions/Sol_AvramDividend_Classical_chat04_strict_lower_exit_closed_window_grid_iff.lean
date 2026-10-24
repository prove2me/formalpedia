-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_lower_exit_closed_window_grid_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:54:05.885429+00:00
-- url     : https://prove2.me/submissions/d1bd13df-2a0d-476b-a02b-e8d4b58bb110

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_lower_exit_right_interval
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket
import Mathlib.Data.NNReal.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-! Every strict downward crossing on a deterministic closed subinterval
is detected at its terminal point or an interior reciprocal-natural grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    (∃ t : ℝ≥0, s ≤ t ∧ t ≤ u ∧ X.X t ω < lower) ↔
    (X.X u ω < lower ∨ ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ,
      s ≤ (k : ℝ≥0) * (n : ℝ≥0)⁻¹ ∧
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < u ∧
      X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω < lower) := by
  constructor
  · rintro ⟨t, hst, htu, hbad⟩
    by_cases hlt : t < u
    · obtain ⟨r, htr, hright⟩ :=
        chat03_strict_lower_exit_right_interval X ω t lower hbad
      have htarget : t < min r u := lt_min htr hlt
      have hδ : 0 < min r u - t := tsub_pos_iff_lt.mpr htarget
      obtain ⟨n, hn, hnlt⟩ := NNReal.exists_nat_pos_inv_lt hδ
      let h : ℝ≥0 := (n : ℝ≥0)⁻¹
      have hh : 0 < h := inv_pos.mpr (by exact_mod_cast hn)
      obtain ⟨hle, hhi⟩ :=
        chat03_nnreal_grid_ceiling_bracket t h hh
      have htplus : t + h < min r u := by
        calc
          t + h < t + (min r u - t) := by
            simpa only [h, add_comm] using (add_lt_add_left hnlt t)
          _ = min r u := add_tsub_cancel_of_le htarget.le
      have hgrid : (Nat.ceil (t / h) : ℝ≥0) * h < min r u :=
        hhi.trans htplus
      right
      refine ⟨n, hn, Nat.ceil (t / h), ?_, ?_, ?_⟩
      · simpa only [h] using hst.trans hle
      · simpa only [h] using hgrid.trans_le (min_le_right r u)
      · simpa only [h] using
          hright _ hle (hgrid.trans_le (min_le_left r u))
    · left
      have heq : t = u := le_antisymm htu (le_of_not_gt hlt)
      simpa only [heq] using hbad
  · rintro (hu | ⟨n, hn, k, hsk, hku, hkbad⟩)
    · exact ⟨u, hsu, le_rfl, hu⟩
    · exact ⟨(k : ℝ≥0) * (n : ℝ≥0)⁻¹,
        hsk, le_of_lt hku, hkbad⟩
