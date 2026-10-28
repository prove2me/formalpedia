-- Prove2me | solution 1 for AvramDividend.Classical.chat04_scaleFunction_measurable_of_punctured_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:59:21.295524+00:00
-- url     : https://prove2.me/submissions/4bf8c8ea-b2a7-4a99-9f15-ac1e9877558d

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The scale function is Borel measurable, including its possible jump at zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Measurable W := by
  have hcont : ContinuousOn W {z : ℝ | z ≠ 0} := by
    intro z hz
    exact (scaleFunction_continuousAt_away_zero X q W hW z hz).continuousWithinAt
  exact measurable_of_measurable_on_compl_singleton (0 : ℝ)
    hcont.domRestrict.measurable
