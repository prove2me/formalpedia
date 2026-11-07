-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_uncapped_band_eventually_contains_positive_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:58:04.045208+00:00
-- url     : https://prove2.me/submissions/085a084d-0598-4442-bb51-72489ffc03df

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
noncomputable section

/-- Every positive reserve eventually lies in each refining uncapped source band. -/
theorem solution (y : ℝ) (hy : 0 < y) :
    ∃ N : ℕ, ∀ n ≥ N,
      y ∈ Icc (((1 : ℝ) / ((n : ℝ) + 1)) / 2) ((n : ℝ) + 2) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max y (1 / (2 * y)))
  refine ⟨N, ?_⟩
  intro n hn
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hL : 1 / (2 * y) < (n : ℝ) + 1 := by
    have h := lt_of_le_of_lt (le_max_right y (1 / (2 * y))) hN
    linarith
  have hU : y < (n : ℝ) + 2 := by
    have h := lt_of_le_of_lt (le_max_left y (1 / (2 * y))) hN
    linarith
  have h2y : (0 : ℝ) < 2 * y := by positivity
  have hmul : 1 < y * (2 * ((n : ℝ) + 1)) := by
    have h := (div_lt_iff₀ h2y).1 hL
    nlinarith
  constructor
  · change (1 : ℝ) / ((n : ℝ) + 1) / 2 ≤ y
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
    nlinarith
  · exact le_of_lt hU
