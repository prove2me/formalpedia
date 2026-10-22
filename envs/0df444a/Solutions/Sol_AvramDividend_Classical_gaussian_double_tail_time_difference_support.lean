-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_time_difference_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T21:00:54.080159+00:00
-- url     : https://prove2.me/submissions/10cb09f5-4223-468d-9c66-865403a4d0f3

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- The difference of two positive-time double-tail atoms is supported
on jumps at least as large as the common positive-time lower bound. -/
theorem solution (μ : Measure ℝ) (ε φ s t : ℝ)
    (hs : ε ≤ s) (ht : ε ≤ t) :
    (∫⁻ z : ℝ, ENNReal.ofReal
      (|(if 0 < t ∧ t < z then (z - t) * Real.exp (-φ * z) else 0) -
        (if 0 < s ∧ s < z then (z - s) * Real.exp (-φ * z) else 0)|) ∂μ) =
    (∫⁻ z in Ici ε, ENNReal.ofReal
      (|(if 0 < t ∧ t < z then (z - t) * Real.exp (-φ * z) else 0) -
        (if 0 < s ∧ s < z then (z - s) * Real.exp (-φ * z) else 0)|) ∂μ) := by
  have hfun :
      (fun z : ℝ => ENNReal.ofReal
        (|(if 0 < t ∧ t < z then (z - t) * Real.exp (-φ * z) else 0) -
          (if 0 < s ∧ s < z then (z - s) * Real.exp (-φ * z) else 0)|)) =
      (Ici ε).indicator (fun z : ℝ => ENNReal.ofReal
        (|(if 0 < t ∧ t < z then (z - t) * Real.exp (-φ * z) else 0) -
          (if 0 < s ∧ s < z then (z - s) * Real.exp (-φ * z) else 0)|)) := by
    funext z
    by_cases hz : ε ≤ z
    · simp [Set.indicator, Set.mem_Ici, hz]
    · have hbad_t : ¬ (0 < t ∧ t < z) := by
        rintro ⟨_, htz⟩
        exact hz (le_trans ht htz.le)
      have hbad_s : ¬ (0 < s ∧ s < z) := by
        rintro ⟨_, hsz⟩
        exact hz (le_trans hs hsz.le)
      simp [Set.indicator, Set.mem_Ici, hz, hbad_t, hbad_s]
  conv_lhs => rw [hfun]
  exact lintegral_indicator (measurableSet_Ici : MeasurableSet (Ici ε)) _
