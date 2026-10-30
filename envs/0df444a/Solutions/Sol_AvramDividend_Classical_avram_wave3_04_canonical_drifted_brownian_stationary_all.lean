-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_canonical_drifted_brownian_stationary_all
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:49:08.594101+00:00
-- url     : https://prove2.me/submissions/486512c0-b7b6-4e5b-b9fe-1c4e7b5a121e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_canonical_drifted_brownian_stationary_strict

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exact canonical Gaussian stationary increments, including zero-duration. -/
theorem solution (s t : ℝ≥0) (hst : s ≤ t) :
    IdentDistrib
      (fun ω : ℝ≥0 → ℝ =>
        (brownian t ω - brownian 0 ω - (t : ℝ)) -
        (brownian s ω - brownian 0 ω - (s : ℝ)))
      (fun ω : ℝ≥0 → ℝ =>
        brownian (t - s) ω - brownian 0 ω - ((t - s : ℝ≥0) : ℝ))
      gaussianLimit gaussianLimit := by
  rcases eq_or_lt_of_le hst with heq | hlt
  · subst t
    have hleft :
        (fun ω : ℝ≥0 → ℝ =>
          (brownian s ω - brownian 0 ω - (s : ℝ)) -
          (brownian s ω - brownian 0 ω - (s : ℝ))) =
        (fun _ => (0 : ℝ)) := by
      funext ω
      ring
    have hright :
        (fun ω : ℝ≥0 → ℝ =>
          brownian (s - s) ω - brownian 0 ω - ((s - s : ℝ≥0) : ℝ)) =
        (fun _ => (0 : ℝ)) := by
      funext ω
      simp
    rw [hleft, hright]
    exact IdentDistrib.refl measurable_const.aemeasurable
  · exact avram_wave3_04_canonical_drifted_brownian_stationary_strict s t hlt
