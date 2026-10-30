-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_canonical_drifted_brownian_stationary_strict
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:40:01.397665+00:00
-- url     : https://prove2.me/submissions/4aafc9c4-2631-46e3-a800-6c9a2a7756d0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_canonical_brownian_realTime_bridge
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_drifted_brownian_stationary_positive_increments

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Genuine canonical projective-limit Brownian increments remain stationary
after subtracting the deterministic drift, at strictly ordered times. -/
theorem solution (s t : ℝ≥0) (hst : s < t) :
    IdentDistrib
      (fun ω : ℝ≥0 → ℝ =>
        (brownian t ω - brownian 0 ω - (t : ℝ)) -
        (brownian s ω - brownian 0 ω - (s : ℝ)))
      (fun ω : ℝ≥0 → ℝ =>
        brownian (t - s) ω - brownian 0 ω - ((t - s : ℝ≥0) : ℝ))
      gaussianLimit gaussianLimit := by
  obtain ⟨W, hW⟩ := canonical_brownian_realTime_bridge
  have hstat :=
    avram_wave3_04_drifted_brownian_stationary_positive_increments W s t hst
  have hleft :
      (fun ω : ℝ≥0 → ℝ =>
        (brownian t ω - brownian 0 ω - (t : ℝ)) -
        (brownian s ω - brownian 0 ω - (s : ℝ))) =
      (fun ω =>
        (W.W (t : ℝ) ω - W.W (s : ℝ) ω) - ((t : ℝ) - (s : ℝ))) := by
    funext ω
    rw [hW t ω, hW s ω]
    ring
  have hright :
      (fun ω : ℝ≥0 → ℝ =>
        brownian (t - s) ω - brownian 0 ω - ((t - s : ℝ≥0) : ℝ)) =
      (fun ω =>
        W.W ((t - s : ℝ≥0) : ℝ) ω - ((t - s : ℝ≥0) : ℝ)) := by
    funext ω
    rw [hW (t - s) ω]
  rw [hleft, hright]
  exact hstat
