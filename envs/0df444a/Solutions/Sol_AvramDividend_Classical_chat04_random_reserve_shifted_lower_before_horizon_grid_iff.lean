-- Prove2me | solution 1 for AvramDividend.Classical.chat04_random_reserve_shifted_lower_before_horizon_grid_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:06:23.167991+00:00
-- url     : https://prove2.me/submissions/285d46c4-5e6a-4a4c-b9e5-abb25bc92905

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_random_reserve_lower_exit_right_interval
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Strict ruin after a clock shift has an exact rational future-grid witness. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (b T : ℝ≥0) :
    (∃ v : ℝ≥0, v < T ∧
      H ω + (X.X (b + v) ω - X.X b ω) < 0) ↔
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T ∧
      H ω +
        (X.X (b + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω - X.X b ω) < 0 := by
  constructor
  · rintro ⟨v, hvT, hvExit⟩
    obtain ⟨u, hbu, hPersist⟩ :=
      chat04_shifted_random_reserve_lower_exit_right_interval
        X H ω b v hvExit
    have hmin : b + v < min u (b + T) :=
      lt_min hbu (add_lt_add_right hvT b)
    have hδ : 0 < min u (b + T) - (b + v) :=
      tsub_pos_iff_lt.mpr hmin
    obtain ⟨n, hn, hnlt⟩ := NNReal.exists_nat_pos_inv_lt hδ
    let h : ℝ≥0 := (n : ℝ≥0)⁻¹
    have hh : 0 < h := inv_pos.mpr (by exact_mod_cast hn)
    obtain ⟨hlo, hhi⟩ :=
      chat03_nnreal_grid_ceiling_bracket v h hh
    have hLess : b + (v + h) < min u (b + T) := by
      calc
        b + (v + h) = (b + v) + h := by ac_rfl
        _ < (b + v) + (min u (b + T) - (b + v)) :=
          add_lt_add_right hnlt (b + v)
        _ = min u (b + T) := add_tsub_cancel_of_le hmin.le
    let k : ℕ := Nat.ceil (v / h)
    have hkLess : b + (k : ℝ≥0) * h < min u (b + T) :=
      (add_lt_add_right hhi b).trans hLess
    have hkT : (k : ℝ≥0) * h < T := by
      have hsum : b + (k : ℝ≥0) * h < b + T :=
        hkLess.trans_le (min_le_right _ _)
      exact (add_lt_add_iff_left b).mp hsum
    have hkExit :
        H ω + (X.X (b + (k : ℝ≥0) * h) ω - X.X b ω) < 0 :=
      hPersist ((k : ℝ≥0) * h) (add_le_add_right hlo b)
        (hkLess.trans_le (min_le_left _ _))
    refine ⟨n, hn, k, ?_, ?_⟩
    · simpa only [h] using hkT
    · simpa only [h] using hkExit
  · rintro ⟨n, _, k, hT, hExit⟩
    exact ⟨(k : ℝ≥0) * (n : ℝ≥0)⁻¹, hT, hExit⟩
