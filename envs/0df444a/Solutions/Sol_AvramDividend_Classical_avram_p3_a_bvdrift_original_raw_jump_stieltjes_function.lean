-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_stieltjes_function
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:43:39.5011+00:00
-- url     : https://prove2.me/submissions/e26414f9-823e-4878-b09f-e172b2d5c994

import Mathlib
import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_right_continuous
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_right_tendsto_to_continuousWithinAt_Ici

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The actual cumulative raw negative-jump series is a Stieltjes function. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ F : StieltjesFunction ℝ≥0, ∀ t : ℝ≥0,
      F t = (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_jump_cumulative_monotone X hBV,
      avram_p3_a_bvdrift_original_raw_jump_cumulative_right_continuous X hBV]
    with ω hmono hright
  let J : ℝ≥0 → ℝ := fun t =>
    (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)
  have hJmono : Monotone J := hmono
  have hJright : ∀ t : ℝ≥0, ContinuousWithinAt J (Ici t) t := by
    intro t
    exact avram_p3_a_bvdrift_right_tendsto_to_continuousWithinAt_Ici J t (hright t)
  refine ⟨StieltjesFunction.mk J hJmono hJright, ?_⟩
  intro t
  rfl
