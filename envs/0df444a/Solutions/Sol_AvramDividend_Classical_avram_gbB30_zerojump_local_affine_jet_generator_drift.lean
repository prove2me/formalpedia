-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB30_zerojump_local_affine_jet_generator_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:19:04.120196+00:00
-- url     : https://prove2.me/submissions/7f9c473d-6689-4080-b387-314dc581d9f6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_zero_jump_generator_eq_gaussian_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (V : ℝ → ℝ) (y : ℝ)
    (hfirst : deriv V y = 1)
    (hsecond : iteratedDeriv 2 V y = 0) :
    X.GeneratorIntegrable V y ∧ X.generator V y = X.c := by
  constructor
  · change IntegrableOn _ (Iio (0 : ℝ)) X.ν
    apply IntegrableOn.of_measure_zero
    simp [hν]
  · rw [avram_p4_f11_zero_jump_generator_eq_gaussian_drift X hν V y,
        hfirst, hsecond]
    ring
