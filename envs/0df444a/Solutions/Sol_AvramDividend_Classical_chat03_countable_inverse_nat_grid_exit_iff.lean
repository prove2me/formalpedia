-- Prove2me | solution 1 for AvramDividend.Classical.chat03_countable_inverse_nat_grid_exit_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T23:08:27.748792+00:00
-- url     : https://prove2.me/submissions/db325f90-75a1-4b21-8811-b5ebbd1c7120

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_exit_right_interval
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
Every continuous-time strict two-sided exit is witnessed at some point
of a countable family of inverse-natural uniform grids, by pathwise
right-continuity and a direct ceiling approximation.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) :
    (∃ t : ℝ≥0, X.X t ω < lower ∨ upper < X.X t ω) ↔
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ,
      X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω < lower ∨
        upper < X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨u, htu, hright⟩ :=
      chat03_strict_exit_right_interval X ω t lower upper ht
    have hδ : 0 < u - t := tsub_pos_iff_lt.mpr htu
    obtain ⟨n, hn, hnlt⟩ := NNReal.exists_nat_pos_inv_lt hδ
    let h : ℝ≥0 := (n : ℝ≥0)⁻¹
    have hh : 0 < h := inv_pos.mpr (by exact_mod_cast hn)
    obtain ⟨hle, hhi⟩ :=
      chat03_nnreal_grid_ceiling_bracket t h hh
    have htplus : t + h < u := by
      calc
        t + h = h + t := add_comm _ _
        _ < (u - t) + t := by simpa only [h] using add_lt_add_left hnlt t
        _ = t + (u - t) := add_comm _ _
        _ = u := add_tsub_cancel_of_le htu.le
    refine ⟨n, hn, Nat.ceil (t / h), ?_⟩
    exact hright _ hle (hhi.trans htplus)
  · rintro ⟨n, _, k, hk⟩
    exact ⟨(k : ℝ≥0) * (n : ℝ≥0)⁻¹, hk⟩

