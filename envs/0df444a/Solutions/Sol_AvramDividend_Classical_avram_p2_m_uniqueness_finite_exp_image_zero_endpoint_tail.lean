-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_finite_exp_image_zero_endpoint_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:23:01.402427+00:00
-- url     : https://prove2.me/submissions/bb5978e8-61d0-49a9-876e-8b9f22812bd3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_finite_real_left_tail_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_exp_image_far_left_cutoff_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical

/-- A finite exponential image has vanishing mass in a shrinking
neighbourhood of the inaccessible zero endpoint. -/
theorem solution (σ : Measure ℝ) [IsFiniteMeasure σ] :
    Tendsto (fun n : ℕ => (σ.map Real.exp)
      (Iic (Real.exp (-(n : ℝ))))) atTop (𝓝 0) := by
  simpa only [avram_p2_m_uniqueness_exp_image_far_left_cutoff_identity]
    using avram_p2_m_uniqueness_finite_real_left_tail_tendsto_zero σ
