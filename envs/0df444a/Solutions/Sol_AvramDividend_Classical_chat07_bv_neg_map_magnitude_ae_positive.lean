-- Prove2me | solution 1 for AvramDividend.Classical.chat07_bv_neg_map_magnitude_ae_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T08:13:12.793133+00:00
-- url     : https://prove2.me/submissions/09f38ef6-d61e-4c25-89e5-11c0a243fa19

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Negating strictly negative Lévy jumps yields a positive-magnitude image almost everywhere. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ᵐ r ∂((X.ν.restrict (Iio (0 : ℝ))).map (fun y : ℝ => -y)),
      (0 : ℝ) < r := by
  have hneg : Measurable (fun y : ℝ => -y) := measurable_neg
  have hpre : ∀ᵐ y ∂(X.ν.restrict (Iio (0 : ℝ))),
      (0 : ℝ) < -y := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    change y < (0 : ℝ) at hy
    exact neg_pos.mpr hy
  exact (ae_map_iff hneg.aemeasurable
    (measurableSet_lt measurable_const measurable_id)).mpr hpre
