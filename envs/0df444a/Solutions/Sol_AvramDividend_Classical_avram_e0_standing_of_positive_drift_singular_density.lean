-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_standing_of_positive_drift_singular_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:37:44.385336+00:00
-- url     : https://prove2.me/submissions/862b4649-4355-4739-ba6c-c7c7602b6ea0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gen15_singular_density_negative_support_ac
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Assemble the original Avram Standing assumptions for the
nonmonotone positive-drift singular negative-jump model. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (hpos : 0 < X.drift) (hne : X.ν ≠ 0)
    (hint : Integrable (X.X 1) P) :
    X.Standing := by
  refine ⟨?_, hint, ?_⟩
  · intro hmono
    rcases hmono.2 with hle | hzero
    · exact (not_le_of_gt hpos) hle
    · exact hne hzero
  · right
    right
    rw [hν]
    exact AvramDividend.Classical.avram_gen15_singular_density_negative_support_ac.2
