-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_residual_increment_positive_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:41:42.963094+00:00
-- url     : https://prove2.me/submissions/b8f430fa-9837-4e88-b6b1-abcb4a1c78e4

import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_increment_zero_probability
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_increment_ae_fixed_times
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Positive drift-residual increments obey the finite-activity exponential event law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) :
    P.real {ω : Ω | 0 <
      ((t : ℝ) * X.drift - X.X t ω) -
      ((s : ℝ) * X.drift - X.X s ω)} =
        1 - Real.exp (-(((t - s : ℝ≥0) : ℝ) *
          (X.ν (Iio (0 : ℝ))).toReal)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let D : Ω → ℝ := fun ω =>
    ((t : ℝ) * X.drift - X.X t ω) -
      ((s : ℝ) * X.drift - X.X s ω)
  have hMeas : Measurable D :=
    (measurable_const.sub (X.adapted.measurable)).sub
      (measurable_const.sub (X.adapted.measurable))
  have hNonneg : ∀ᵐ ω ∂P, 0 ≤ D ω := by
    filter_upwards [bv_actual_levy_drift_increment_ae_fixed_times X hBV s t hst]
      with ω hw
    have hcoe : (((t - s : ℝ≥0) : ℝ)) =
      (t : ℝ) - (s : ℝ) := NNReal.coe_sub hst
    rw [hcoe] at hw
    dsimp [D]
    nlinarith
  have hset : {ω : Ω | 0 < D ω} =ᵐ[P] ({ω : Ω | D ω = 0}ᶜ) := by
    filter_upwards [hNonneg] with ω hw
    change (0 < D ω) = (¬ D ω = 0)
    apply propext
    constructor
    · exact ne_of_gt
    · intro hn
      exact lt_of_le_of_ne hw (Ne.symm hn)
  have hMeasSet : MeasurableSet {ω : Ω | D ω = 0} :=
    hMeas (measurableSet_singleton 0)
  have hp : P.real {ω : Ω | 0 < D ω} =
      1 - P.real {ω : Ω | D ω = 0} := by
    rw [measureReal_congr hset]
    exact probReal_compl_eq_one_sub hMeasSet
  change P.real {ω : Ω | 0 < D ω} = _
  rw [hp]
  congr 1
  exact bv_actual_residual_increment_zero_probability X hBV hFinite s t hst
