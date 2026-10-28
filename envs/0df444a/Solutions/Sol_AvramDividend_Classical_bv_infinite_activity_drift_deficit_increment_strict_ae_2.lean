-- Prove2me | solution 2 for AvramDividend.Classical.bv_infinite_activity_drift_deficit_increment_strict_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:44:23.738401+00:00
-- url     : https://prove2.me/submissions/2c10ba10-03bc-43b4-80d9-7ef0138ca054

import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_drift_deficit_increment_zero_atom
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual infinite-activity BV drift deficit strictly increases over any fixed interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (s t : ℝ≥0) (hst : s < t) :
    ∀ᵐ ω ∂P,
      X.drift * (s : ℝ) - X.X s ω <
        X.drift * (t : ℝ) - X.X t ω := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hZeroReal :=
    bv_infinite_activity_drift_deficit_increment_zero_atom
      X hBV hνinf s t hst
  have hNull : P {ω : Ω |
      (X.drift * (t : ℝ) - X.X t ω) -
        (X.drift * (s : ℝ) - X.X s ω) = 0} = 0 :=
    (measureReal_eq_zero_iff).mp hZeroReal
  have hNotZero : ∀ᵐ ω ∂P,
      (X.drift * (t : ℝ) - X.X t ω) -
        (X.drift * (s : ℝ) - X.X s ω) ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using hNull
  filter_upwards
    [hNotZero, bv_drift_deficit_ae_monotone_all_times X hBV]
    with ω hne hMono
  have hNonneg :
      0 ≤ (X.drift * (t : ℝ) - X.X t ω) -
        (X.drift * (s : ℝ) - X.X s ω) :=
    sub_nonneg.mpr (hMono (le_of_lt hst))
  have hPos := lt_of_le_of_ne hNonneg (Ne.symm hne)
  exact sub_pos.mp hPos
