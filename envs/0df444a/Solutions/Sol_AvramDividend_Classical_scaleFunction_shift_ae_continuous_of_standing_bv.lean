-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_shift_ae_continuous_of_standing_bv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:34:26.965206+00:00
-- url     : https://prove2.me/submissions/bcd32495-42db-4264-8ddb-258c95f26c87

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_levyMeasure_singleton_null_of_standing_boundedVariation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x) :
    ∀ᵐ y ∂(X.ν.restrict (Iio 0)), ContinuousAt W (x + y) := by
  have hnull : X.ν {(-x)} = 0 :=
    levyMeasure_singleton_null_of_standing_boundedVariation X hX hbv (-x)
  have hnull_restr : (X.ν.restrict (Iio 0)) {(-x)} = 0 := by
    have hle :
        (X.ν.restrict (Iio 0)) {(-x)} ≤ X.ν {(-x)} :=
      (Measure.le_iff'.1 Measure.restrict_le_self) _
    exact nonpos_iff_eq_zero.mp (hle.trans_eq hnull)
  have hnot : ∀ᵐ y ∂(X.ν.restrict (Iio 0)), y ≠ -x := by
    apply ae_iff.mpr
    simpa only [not_ne_iff, Set.setOf_eq_eq_singleton] using hnull_restr
  filter_upwards [hnot] with y hy
  have hshift : x + y ≠ 0 := by
    intro hxy
    apply hy
    linarith
  exact scaleFunction_continuousAt_away_zero X q W hW (x + y) hshift
