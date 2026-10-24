-- Prove2me | solution 1 for AvramDividend.Classical.chat04_stieltjes_Ioc_eq_of_right_continuous_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:03:13.324175+00:00
-- url     : https://prove2.me/submissions/b3e23810-530b-4f79-9615-3ab91bcdc53b

import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_rightLimit_eq_of_monotone_right_continuous
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Matching record increments give the same Stieltjes mass on a fixed interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D E : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hE : IsDividendStrategy 𝓕 E)
    (ω : Ω) (a b : ℝ≥0)
    (hmD : Monotone (fun s => D s ω))
    (hmE : Monotone (fun s => E s ω))
    (hrDa : ContinuousWithinAt (fun s => D s ω) (Set.Ici a) a)
    (hrDb : ContinuousWithinAt (fun s => D s ω) (Set.Ici b) b)
    (hrEa : ContinuousWithinAt (fun s => E s ω) (Set.Ici a) a)
    (hrEb : ContinuousWithinAt (fun s => E s ω) (Set.Ici b) b)
    (hinc : D b ω - D a ω = E b ω - E a ω) :
    dividendMeasure D ω (Set.Ioc (a : ℝ) (b : ℝ)) =
      dividendMeasure E ω (Set.Ioc (a : ℝ) (b : ℝ)) := by
  rw [dividendMeasure_Ioc_rightLimit D hD ω a b]
  rw [dividendMeasure_Ioc_rightLimit E hE ω a b]
  rw [rightLimit_eq_of_monotone_right_continuous D ω b hmD hrDb]
  rw [rightLimit_eq_of_monotone_right_continuous D ω a hmD hrDa]
  rw [rightLimit_eq_of_monotone_right_continuous E ω b hmE hrEb]
  rw [rightLimit_eq_of_monotone_right_continuous E ω a hmE hrEa]
  exact congrArg ENNReal.ofReal hinc
