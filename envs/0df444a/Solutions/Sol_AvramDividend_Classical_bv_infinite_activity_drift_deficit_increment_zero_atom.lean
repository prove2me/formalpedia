-- Prove2me | solution 1 for AvramDividend.Classical.bv_infinite_activity_drift_deficit_increment_zero_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:35:52.961171+00:00
-- url     : https://prove2.me/submissions/719a8512-350d-4055-8264-f9242965b7c2

import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_drift_deficit_zero_atom
import Theorems.Thm_AvramDividend_Classical_actual_levy_drift_deficit_stationary_increment_law
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Every positive-duration increment of the actual infinite-activity BV drift deficit has no zero atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (s t : ℝ≥0) (hst : s < t) :
    P.real {ω : Ω |
        (X.drift * (t : ℝ) - X.X t ω) -
          (X.drift * (s : ℝ) - X.X s ω) = 0} = 0 := by
  have hDur : 0 < t - s := tsub_pos_iff_lt.mpr hst
  have hIdent :=
    actual_levy_drift_deficit_stationary_increment_law
      X s t (le_of_lt hst)
  have hSet : MeasurableSet {z : ℝ | z = 0} :=
    measurableSet_singleton 0
  have hMass := hIdent.measure_mem_eq hSet
  have hShift :
      P.real {ω : Ω |
        (X.drift * (t : ℝ) - X.X t ω) -
          (X.drift * (s : ℝ) - X.X s ω) = 0} =
      P.real {ω : Ω |
        X.drift * ((t - s : ℝ≥0) : ℝ) -
          X.X (t - s) ω = 0} := by
    exact congrArg ENNReal.toReal (by
      simpa only [Set.preimage, Set.mem_setOf_eq] using hMass)
  calc
    P.real {ω : Ω |
        (X.drift * (t : ℝ) - X.X t ω) -
          (X.drift * (s : ℝ) - X.X s ω) = 0} =
      P.real {ω : Ω |
        X.drift * ((t - s : ℝ≥0) : ℝ) -
          X.X (t - s) ω = 0} := hShift
    _ = 0 := by
      simpa only [mul_comm] using
        (bv_infinite_activity_drift_deficit_zero_atom
          X hBV hνinf (t - s) hDur)
