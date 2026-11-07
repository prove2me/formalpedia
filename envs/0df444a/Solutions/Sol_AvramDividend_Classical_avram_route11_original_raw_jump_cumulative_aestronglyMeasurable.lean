-- Prove2me | solution 1 for AvramDividend.Classical.avram_route11_original_raw_jump_cumulative_aestronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:51:21.382371+00:00
-- url     : https://prove2.me/submissions/afd39ed1-dc27-4cf0-9d20-9fa5c52aed11

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_actual_jump_total_aemeasurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The real raw jump sum agrees almost everywhere with its measurable ENNReal total. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (t : ℝ≥0) :
    AEStronglyMeasurable
      (fun ω : Ω =>
        ∑' v : ℝ≥0,
          if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0) P := by
  have hsum : ∀ᵐ ω ∂P,
      (∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ t then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal =
      (∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0) := by
    filter_upwards
      [avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum X hBV]
      with ω hω
    exact (hω 0 t (by exact zero_le)).2
  exact (avram_p3_a_bvdrift_actual_jump_total_aemeasurable
    X hBV t).aestronglyMeasurable.congr hsum
