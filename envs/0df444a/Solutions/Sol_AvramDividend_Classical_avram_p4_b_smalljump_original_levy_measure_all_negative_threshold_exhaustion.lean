-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_levy_measure_all_negative_threshold_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:44:57.6715+00:00
-- url     : https://prove2.me/submissions/90092d2c-0955-4f85-8b6b-5d3b55ac0f06

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual original Lévy mark intensity on negative marks exhausts
monotonically by the same physical jump-size cutoffs as its source count. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    X.ν (Iio (0 : ℝ)) =
      ⨆ n : ℕ, X.ν {z : ℝ |
        z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z} := by
  let B : ℕ → Set ℝ := fun n =>
    {z : ℝ | z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z}
  have hMon : Monotone B := by
    intro n m hnm z hz
    refine ⟨hz.1, ?_⟩
    have hm : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hnm 1
    have hRec : (1 : ℝ) / ((m : ℝ) + 1) ≤
        1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hm
    exact hRec.trans hz.2
  have hUnion : (⋃ n, B n) = Iio (0 : ℝ) := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_Iio, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hn⟩
      exact hn.1
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < -z by linarith)
      exact ⟨n, hz, le_of_lt hn⟩
  calc
    X.ν (Iio (0 : ℝ)) = X.ν (⋃ n, B n) := by rw [hUnion]
    _ = ⨆ n, X.ν (B n) := hMon.measure_iUnion
