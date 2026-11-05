-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_exp_image_strict_lower_band_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:22:04.691527+00:00
-- url     : https://prove2.me/submissions/42708fd1-c512-4039-ae23-85e721da670b

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Exact exponential transport of interval mass, with strict lower
endpoint preserved. This applies to finite negative-mark bands. -/
theorem solution (σ : Measure ℝ) (a b : ℝ) :
    (σ.map Real.exp) (Ioc (Real.exp a) (Real.exp b)) =
      σ (Ioc a b) := by
  rw [Measure.map_apply Real.measurable_exp measurableSet_Ioc]
  congr 1
  ext x
  simp only [mem_preimage, mem_Ioc, Real.exp_lt_exp, Real.exp_le_exp]
