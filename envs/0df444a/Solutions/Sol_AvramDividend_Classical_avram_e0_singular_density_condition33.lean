-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_singular_density_condition33
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:35:02.30004+00:00
-- url     : https://prove2.me/submissions/e3e16e3c-7a58-4073-8e7e-612db2d4ea4d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gen15_singular_density_negative_support_ac
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! The singular negative-jump measure fulfils the absolutely continuous
alternative in the original Avram Condition33. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0)) :
    X.Condition33 := by
  right
  right
  rw [hν]
  exact AvramDividend.Classical.avram_gen15_singular_density_negative_support_ac.2
