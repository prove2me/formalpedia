-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_zero_horizon_chronological_pairs_empty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:51:54.898193+00:00
-- url     : https://prove2.me/submissions/e704de1a-55b6-48d8-b8ca-ab79271a04e1

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

/-- At zero horizon, the original source negative-band jump-time set has no chronological pairs. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite
        X ω 0 n).toFinset
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card = 0 := by
  classical
  let hfin := avram_wave7_06_original_negative_band_marked_times_finite
    X ω 0 n
  let F : Finset ℝ≥0 := hfin.toFinset
  have hF : F = ∅ := by
    ext u
    constructor
    · intro hu
      have hu' := (Set.Finite.mem_toFinset hfin).mp hu
      exact (not_lt_of_ge hu'.2.1 hu'.1).elim
    · intro hu
      simp at hu
  change ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card = 0
  rw [hF]
  simp
