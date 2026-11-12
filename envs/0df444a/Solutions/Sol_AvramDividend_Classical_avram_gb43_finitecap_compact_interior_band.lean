-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb43_finitecap_compact_interior_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:56:25.024303+00:00
-- url     : https://prove2.me/submissions/9e457443-bdea-47b8-80b1-fff50877db66

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Every finite-cap clipped Gaussian interval lies inside the open C²
domain, with a uniform top-cap margin at each fixed cutoff index. -/
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    let a : ℝ := δ / 2
    let b : ℝ := C.toReal *
      (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
      Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
  let a : ℝ := δ / 2
  let b : ℝ := C.toReal *
    (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  change IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
    Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}
  constructor
  · change IsOpen (Ioi (0 : ℝ) ∩ ENNReal.ofReal ⁻¹' Iio C)
    exact isOpen_Ioi.inter (isOpen_Iio.preimage ENNReal.continuous_ofReal)
  · have ha : 0 < a := by dsimp [a]; linarith
    have hCpos : 0 < C.toReal :=
      ENNReal.toReal_pos (ne_of_gt hC) hFiniteCap
    have hf : (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) < 1 := by
      apply (div_lt_one (by positivity)).2
      exact_mod_cast Nat.lt_succ_self (j + 1)
    have hb : b < C.toReal := by
      dsimp [b]
      nlinarith [mul_lt_mul_of_pos_left hf hCpos]
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
    exact ⟨hy0,
      (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy0) hFiniteCap).2
        (lt_of_le_of_lt hy.2 hb)⟩
