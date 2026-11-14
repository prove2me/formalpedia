-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb71_finite_original_Levy_negative_mark_integral_norm_le_kernel_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:08:25.506326+00:00
-- url     : https://prove2.me/submissions/2abfd5f2-87a6-4421-951c-cffbd08f1b55

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem solution
    (ν : Measure ℝ) (S : Set ℝ) (hS : MeasurableSet S)
    (hMass : ν S < ⊤) (f : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ z ∈ S, |f z| ≤ K) :
    ‖∫ z in S, f z ∂ν‖ ≤ K * (ν S).toReal := by
  apply norm_setIntegral_le_of_norm_le_const_ae' hMass
  filter_upwards [] with z
  intro hz
  simpa only [Real.norm_eq_abs] using hBound z hz
