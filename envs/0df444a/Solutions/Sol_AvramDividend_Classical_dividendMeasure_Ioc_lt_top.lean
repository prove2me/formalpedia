-- Prove2me | solution 1 for AvramDividend.Classical.dividendMeasure_Ioc_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T23:23:50.568643+00:00
-- url     : https://prove2.me/submissions/d0e9efea-1b0b-49e2-b595-bbbf07ee063c

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a b : ℝ) :
    dividendMeasure D ω (Ioc a b) < ⊤ := by
  have hmono : Monotone (fun r : ℝ => D r.toNNReal ω) :=
    (hD.2.1 ω).comp Real.toNNReal_monotone
  unfold dividendMeasure
  rw [dif_pos hmono, StieltjesFunction.measure_Ioc,
    Monotone.stieltjesFunction_eq, Monotone.stieltjesFunction_eq]
  exact ENNReal.ofReal_lt_top

