-- Prove2me | solution 2 for AvramDividend.Classical.avram_p4_f_assembly_original_chronological_pair_zero_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:56:18.679313+00:00
-- url     : https://prove2.me/submissions/84d1b3c9-8842-4f51-90d1-fb54814e9f76

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original source has no strictly positive marked jump before time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω 0 n).toFinset
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card = 0 := by
  intro F
  have hF : (avram_wave7_06_original_negative_band_marked_times_finite X ω 0 n).toFinset = ∅ := by
    ext u
    simp only [Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hu, hu0, _⟩
      exact False.elim ((not_lt_of_ge hu0) hu)
    · intro hu
      simpa using hu
  change (((avram_wave7_06_original_negative_band_marked_times_finite X ω 0 n).toFinset ×ˢ
    (avram_wave7_06_original_negative_band_marked_times_finite X ω 0 n).toFinset).filter
    (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card = 0
  rw [hF]
  simp
