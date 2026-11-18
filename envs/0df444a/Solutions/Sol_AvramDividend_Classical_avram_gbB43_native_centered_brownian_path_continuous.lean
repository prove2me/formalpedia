-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB43_native_centered_brownian_path_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:04:21.905679+00:00
-- url     : https://prove2.me/submissions/ed6734ec-8c53-478e-83b6-27ac519ad406

import Mathlib
import Theorems.Thm_AvramDividend_Classical_canonical_drifted_brownian_zero_continuous
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The centered native Brownian coordinates have continuous sample paths. -/
theorem solution (ω : ℝ≥0 → ℝ) :
    Continuous (fun t : ℝ≥0 =>
      ProbabilityTheory.brownian t ω - ProbabilityTheory.brownian 0 ω) := by
  have hshift := (canonical_drifted_brownian_zero_continuous ω).2
  have htime : Continuous (fun t : ℝ≥0 => (t : ℝ)) := by fun_prop
  have hf :
      (fun t : ℝ≥0 =>
        (ProbabilityTheory.brownian t ω -
          ProbabilityTheory.brownian 0 ω - (t : ℝ)) + (t : ℝ)) =
      (fun t : ℝ≥0 =>
        ProbabilityTheory.brownian t ω -
          ProbabilityTheory.brownian 0 ω) := by
    funext t
    ring
  rw [← hf]
  exact hshift.add htime
