-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_harmonic_negative_band_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:21:09.475039+00:00
-- url     : https://prove2.me/submissions/753d99c1-6a97-4a8a-9e29-8c3578bd2a40

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_negative_band_exhaustion_from_cutoffs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Explicit harmonic cutoffs exhaust every strictly negative Borel mark set. -/
theorem solution
    (B : Set ℝ) (hB : MeasurableSet B)
    (hBneg : B ⊆ Iio (0 : ℝ)) :
    (∀ n : ℕ, MeasurableSet (B ∩ Iic (-(1 / ((n : ℝ) + 1))))) ∧
    Monotone (fun n : ℕ => B ∩ Iic (-(1 / ((n : ℝ) + 1)))) ∧
    (⋃ n : ℕ, B ∩ Iic (-(1 / ((n : ℝ) + 1)))) = B ∧
    (∀ n : ℕ, ∃ δ : ℝ, 0 < δ ∧ B ∩ Iic (-(1 / ((n : ℝ) + 1))) ⊆ Iic (-δ)) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    positivity
  have hεAnti : Antitone ε := by
    intro i j hij
    dsimp [ε]
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hijReal : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    have hle : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by linarith
    exact one_div_le_one_div_of_le hi hle
  have hεzero : Tendsto ε atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  exact AvramDividend.Classical.avram_p2_c_borel_negative_band_exhaustion_from_cutoffs
    B hB hBneg ε hεpos hεAnti hεzero
