-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_exp_image_far_left_cutoff_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:05:10.521304+00:00
-- url     : https://prove2.me/submissions/d6c59a78-addd-4396-9ecb-a40ec0a1d5f4

import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- The exact inverse image of an exponentially shrinking positive
endpoint neighbourhood is a far-left real half-line. -/
theorem solution (σ : Measure ℝ) (n : ℕ) :
    (σ.map Real.exp) (Iic (Real.exp (-(n : ℝ)))) =
      σ (Iic (-(n : ℝ))) := by
  rw [Measure.map_apply Real.measurable_exp measurableSet_Iic]
  congr 1
  ext x
  simp only [mem_preimage, mem_Iic, Real.exp_le_exp]
