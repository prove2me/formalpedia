-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_negative_mark_JL_compensator_integral_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:46:10.993591+00:00
-- url     : https://prove2.me/submissions/a7d9bc69-5b8b-4ed3-aa46-fc757ef9c8be

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_negative_mark_JL_cutoff_exact_kernel
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (μ : Measure ℝ) (η : ℝ) (S d : ℝ → ℝ)
    (hη : 0 < η) (hηone : η < 1)
    (hneg : ∀ᵐ z ∂μ, z < 0)
    (hH : Integrable (fun z => S z -
      (if -1 < z then z * d z else 0)) μ)
    (hL : Integrable (fun z => if z ∈ Ioo (-1 : ℝ) (-η) then
      z * d z else 0) μ) :
    (∫ z, S z - (if -1 < z then z * d z else 0) ∂μ) +
    (∫ z, (if z ∈ Ioo (-1 : ℝ) (-η) then z * d z else 0) ∂μ) =
    (∫ z, S z - (if -η ≤ z then z * d z else 0) ∂μ) := by
  rw [← integral_add hH hL]
  apply integral_congr_ae
  filter_upwards [hneg] with z hz
  exact
    AvramDividend.Classical.avram_pj_workerC_negative_mark_JL_cutoff_exact_kernel
      η z (S z) (d z) hη hηone hz

