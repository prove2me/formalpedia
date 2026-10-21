-- Prove2me | solution 1 for AvramDividend.Classical.chat03_lower_before_horizon_countable_grid_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:34:02.743665+00:00
-- url     : https://prove2.me/submissions/11ebc0be-ce2f-42f6-83df-5bb76bd5e754

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_lower_exit_right_interval
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
Every strict downward passage before a finite horizon has an
inverse-natural grid witness strictly before that horizon.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower : ℝ) (T : ℝ≥0) :
    (∃ s : ℝ≥0, s < T ∧ X.X s ω < lower) ↔
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T ∧
        X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω < lower := by
  constructor
  · rintro ⟨s, hsT, hsExit⟩
    obtain ⟨u, hsu, hright⟩ :=
      chat03_strict_lower_exit_right_interval X ω s lower hsExit
    have hmin : s < min u T := lt_min hsu hsT
    have hδ : 0 < min u T - s := tsub_pos_iff_lt.mpr hmin
    obtain ⟨n, hn, hnlt⟩ := NNReal.exists_nat_pos_inv_lt hδ
    let h : ℝ≥0 := (n : ℝ≥0)⁻¹
    have hh : 0 < h := inv_pos.mpr (by exact_mod_cast hn)
    obtain ⟨hlo, hhi⟩ :=
      chat03_nnreal_grid_ceiling_bracket s h hh
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
