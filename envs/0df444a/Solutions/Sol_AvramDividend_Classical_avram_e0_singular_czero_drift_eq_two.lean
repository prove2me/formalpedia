-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_singular_czero_drift_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:47:44.111055+00:00
-- url     : https://prove2.me/submissions/3d860456-a88f-4d70-baae-042cbabba4b3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gen15_singular_density_restricted_signed_moment_neg_two
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Convert the proved restricted jump first moment into the physical drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hc : X.c = 0)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0)) :
    X.drift = 2 := by
  change X.c - (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) = 2
  rw [hc, hν, AvramDividend.Classical.avram_gen15_singular_density_restricted_signed_moment_neg_two]
  norm_num
