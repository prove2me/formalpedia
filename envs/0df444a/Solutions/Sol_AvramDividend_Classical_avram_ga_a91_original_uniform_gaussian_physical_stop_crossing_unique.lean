-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a91_original_uniform_gaussian_physical_stop_crossing_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:47:45.407082+00:00
-- url     : https://prove2.me/submissions/18613b8b-753d-4c1f-8474-0f3930508f41

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Physical uniform cells cannot cross a stopping clock at two indices. -/
theorem solution (n m i j : ℕ) (ρ : ℝ≥0)
    (hij : i < j)
    (hi : (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ)
    (hcross : ρ ≤ ((i + 1 : ℕ) : ℝ≥0) *
      ((n : ℝ≥0) / ((m : ℝ≥0) + 1)))
    (hj : (j : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ) :
    False := by
  have hsucc : i + 1 ≤ j := Nat.succ_le_iff.mpr hij
  have hcast : ((i + 1 : ℕ) : ℝ≥0) ≤ (j : ℝ≥0) := by
    exact_mod_cast hsucc
  have hfactor : (0 : ℝ≥0) ≤
      (n : ℝ≥0) / ((m : ℝ≥0) + 1) := by positivity
  have hmul :
      ((i + 1 : ℕ) : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) ≤
      (j : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) :=
    mul_le_mul_of_nonneg_right hcast hfactor
  exact (not_lt_of_ge (hcross.trans hmul)) hj
