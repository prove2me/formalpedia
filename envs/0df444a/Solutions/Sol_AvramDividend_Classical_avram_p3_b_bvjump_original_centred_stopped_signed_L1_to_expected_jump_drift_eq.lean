-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_centred_stopped_signed_L1_to_expected_jump_drift_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:22:38.079943+00:00
-- url     : https://prove2.me/submissions/7efb7477-6f29-4f57-923c-606b83b5862b

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-- A centred L1 stopped jump-minus-compensator cash residual identifies
the expectations of the genuine jump cash and its source compensator. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (J C : Ω → ℝ)
    (hJ : Integrable J P) (hC : Integrable C P)
    (hCentred : Integrable (fun ω => J ω - C ω) P ∧
      (∫ ω, J ω - C ω ∂P) = 0) :
    (∫ ω, J ω ∂P) = (∫ ω, C ω ∂P) := by
  have h := hCentred.2
  rw [integral_sub hJ hC] at h
  exact sub_eq_zero.mp h
