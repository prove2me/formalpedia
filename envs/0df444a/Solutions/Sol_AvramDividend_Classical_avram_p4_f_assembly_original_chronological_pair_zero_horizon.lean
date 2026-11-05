-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_chronological_pair_zero_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:55:09.882812+00:00
-- url     : https://prove2.me/submissions/b1d5857c-d003-4c78-a940-a10d49a30036

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω 0 n).toFinset
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card = 0 := by
  classical
  dsimp
  have hempty :
      (avram_wave7_06_original_negative_band_marked_times_finite X ω 0 n).toFinset = ∅ := by
    ext u
    constructor
    · intro hu
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hu
      exact False.elim ((not_lt_of_ge hu.2.1) hu.1)
    · intro hu
      simp at hu
  simp only [hempty]
  rfl
