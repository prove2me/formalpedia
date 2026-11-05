-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_finite_weighted_image_zero_endpoint_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:34:09.214515+00:00
-- url     : https://prove2.me/submissions/6fa69656-44cb-4747-a36f-7b60e8433549

import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_finite_exp_image_zero_endpoint_tail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped ENNReal

/-- An arbitrary weighted source is finite whenever its exponential
pushforward is finite; its image consequently has vanishing zero tails. -/
theorem solution (σ : Measure ℝ) (w : ℝ → ℝ≥0∞)
    [IsFiniteMeasure ((σ.withDensity w).map Real.exp)] :
    Tendsto (fun n : ℕ => ((σ.withDensity w).map Real.exp)
      (Iic (Real.exp (-(n : ℝ))))) atTop (𝓝 0) := by
  have hmap : ((σ.withDensity w).map Real.exp) univ =
      (σ.withDensity w) univ := by
    rw [Measure.map_apply Real.measurable_exp MeasurableSet.univ]
    simp
  have hfinite : (σ.withDensity w) univ < ⊤ := by
    rw [← hmap]
    exact measure_lt_top ((σ.withDensity w).map Real.exp) univ
  letI : IsFiniteMeasure (σ.withDensity w) := ⟨hfinite⟩
  exact avram_p2_m_uniqueness_finite_exp_image_zero_endpoint_tail
    (σ.withDensity w)
