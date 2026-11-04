-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_tilted_weighted_exponential_pushforward_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:48:35.110185+00:00
-- url     : https://prove2.me/submissions/b9bafce8-8b4d-44d4-af80-0034638364ec

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_all_positive_tilts_fourth_weighted_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The exponentially tilted, fourth-weighted original source law pushed
forward by exp is a finite measure at each time and nonnegative tilt. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    IsFiniteMeasure
      ((P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (ρ * X.X t ω) *
          (Real.exp (X.X t ω) - 1) ^ 4))).map
        (fun ω => Real.exp (X.X t ω))) := by
  have hi : Integrable (fun ω => Real.exp (ρ * X.X t ω) *
      (Real.exp (X.X t ω) - 1) ^ 4) P :=
    avram_p2_original_all_positive_tilts_fourth_weighted_integrable X t ρ hρ
  letI : IsFiniteMeasure
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (ρ * X.X t ω) *
          (Real.exp (X.X t ω) - 1) ^ 4))) :=
    isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral
  exact Measure.isFiniteMeasure_map _ _
