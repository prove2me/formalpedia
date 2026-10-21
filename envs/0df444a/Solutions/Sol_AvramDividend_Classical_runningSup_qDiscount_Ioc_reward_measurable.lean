-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_qDiscount_Ioc_reward_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:23:57.311157+00:00
-- url     : https://prove2.me/submissions/f22df720-1f61-4296-944d-72556b6109b8

import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_restrict_Ioc_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q l u : ℝ) :
    Measurable (fun ω : Ω =>
      ∫⁻ r in Set.Ioc l u,
        ENNReal.ofReal (Real.exp (-(q * r)))
        ∂(dividendMeasure (runningSup X) ω)) := by
  have hw : Measurable (fun r : ℝ =>
      ENNReal.ofReal (Real.exp (-(q * r)))) := by
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg))
  have hmeasure :
      Measurable (fun ω : Ω =>
        (dividendMeasure (runningSup X) ω).restrict (Set.Ioc l u)) :=
    runningSup_dividendMeasure_restrict_Ioc_measurable X l u
  change Measurable (fun ω : Ω =>
    ∫⁻ r, ENNReal.ofReal (Real.exp (-(q * r)))
       ∂(dividendMeasure (runningSup X) ω).restrict (Set.Ioc l u))
  exact (Measure.measurable_lintegral hw).comp hmeasure
