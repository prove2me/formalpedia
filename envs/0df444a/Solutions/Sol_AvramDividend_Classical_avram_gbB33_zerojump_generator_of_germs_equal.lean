-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB33_zerojump_generator_of_germs_equal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:31:56.738145+00:00
-- url     : https://prove2.me/submissions/ccf71e08-8d61-4bb1-bce2-4239a6bf76b9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_zero_jump_generator_eq_gaussian_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (V w : ℝ → ℝ) (y : ℝ)
    (hEv : V =ᶠ[𝓝 y] w) :
    X.generator V y = X.generator w y := by
  have hfirst : deriv V y = deriv w y := hEv.deriv_eq
  have hsecond : iteratedDeriv 2 V y = iteratedDeriv 2 w y := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hEv.deriv.deriv_eq
  rw [avram_p4_f11_zero_jump_generator_eq_gaussian_drift X hν V y,
      avram_p4_f11_zero_jump_generator_eq_gaussian_drift X hν w y,
      hfirst, hsecond]
