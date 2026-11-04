-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_public_reciprocal_borel_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:26:33.221681+00:00
-- url     : https://prove2.me/submissions/fcdebc88-4ced-40d8-848f-fda27013b3c2

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

/-- Every Borel mark set has a monotone separated-negative reciprocal cover. -/
theorem solution (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ C : ℕ → Set ℝ,
      (∀ n, MeasurableSet (C n)) ∧
      Monotone C ∧
      (⋃ n, C n) = B ∩ Iio (0 : ℝ) ∧
      ∀ n, ∃ ε : ℝ, 0 < ε ∧ C n ⊆ Iic (-ε) := by
  let f : ℕ → ℝ := fun n => -(1 / ((n : ℝ) + 1))
  have hlt : ∀ n, f n < 0 := by
    intro n
    exact neg_lt_zero.mpr (one_div_pos.mpr (by positivity))
  have hlim : Tendsto f atTop (𝓝 (0 : ℝ)) := by
    simpa [f] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  have hUnion : (⋃ n : ℕ, Iic (f n)) = Iio (0 : ℝ) :=
    iUnion_Iic_eq_Iio_of_lt_of_tendsto hlt hlim
  have hfmono : Monotone f := by
    intro i j hij
    have hden : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hij 1
    have hfrac : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hden
    exact neg_le_neg hfrac
  let C : ℕ → Set ℝ := fun n => B ∩ Iic (f n)
  have hCm : ∀ n, MeasurableSet (C n) := fun n =>
    hB.inter measurableSet_Iic
  have hCmono : Monotone C := by
    intro i j hij x hx
    exact ⟨hx.1, le_trans hx.2 (hfmono hij)⟩
  have hCover : (⋃ n, C n) = B ∩ Iio (0 : ℝ) := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
      have hcut : x ∈ ⋃ n : ℕ, Iic (f n) :=
        Set.mem_iUnion.mpr ⟨n, hn.2⟩
      rw [hUnion] at hcut
      exact ⟨hn.1, hcut⟩
    · rintro ⟨hxB, hxNeg⟩
      have hcut : x ∈ ⋃ n : ℕ, Iic (f n) := by
        rw [hUnion]
        exact hxNeg
      rcases Set.mem_iUnion.mp hcut with ⟨n, hn⟩
      exact Set.mem_iUnion.mpr ⟨n, ⟨hxB, hn⟩⟩
  have hCsep : ∀ n, ∃ ε : ℝ, 0 < ε ∧ C n ⊆ Iic (-ε) := by
    intro n
    refine ⟨1 / ((n : ℝ) + 1), one_div_pos.mpr (by positivity), ?_⟩
    exact fun x hx => hx.2
  exact ⟨C, hCm, hCmono, hCover, hCsep⟩
