-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_original_finite_horizon_time_probability_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:16:17.139271+00:00
-- url     : https://prove2.me/submissions/46035700-78b1-46f0-bbff-8e809d3732e6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
(((((volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P) Set.univ) < ⊤ := by
  letI : IsProbabilityMeasure P := X.isProbability
  haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))) :=
    Real.isFiniteMeasure_restrict_Icc 0 (T : ℝ)
  haveI : IsFiniteMeasure (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal) :=
    inferInstance
  exact measure_lt_top _ _
