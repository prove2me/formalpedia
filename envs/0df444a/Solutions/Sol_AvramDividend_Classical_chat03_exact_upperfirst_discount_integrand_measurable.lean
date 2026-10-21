-- Prove2me | solution 1 for AvramDividend.Classical.chat03_exact_upperfirst_discount_integrand_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T07:24:33.396205+00:00
-- url     : https://prove2.me/submissions/28697224-f71b-460d-8dd3-7c4f1e1bdfcf

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
The exact ENNReal-valued upper-first discounted payoff integrand
of the allocated stopped-scale identity is measurable, including ties,
infinite clocks and the ENNReal.toReal conversion.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper q : ℝ) :
    Measurable (fun ω : Ω =>
      if twoSidedExitUpTime X upper ω < twoSidedExitDownTime X lower ω
      then ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X upper ω))))
      else 0) := by
  obtain ⟨hUp, hDown⟩ :=
    chat03_both_named_passage_clocks_measurable X lower upper
  have hEvent : MeasurableSet
      {ω : Ω | twoSidedExitUpTime X upper ω <
        twoSidedExitDownTime X lower ω} :=
    measurableSet_lt hUp hDown
  have hTime : Measurable (fun ω : Ω =>
      ENNReal.toReal (twoSidedExitUpTime X upper ω)) :=
    ENNReal.measurable_toReal.comp hUp
  have hExp : Measurable (fun ω : Ω =>
      Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X upper ω)))) :=
    Real.measurable_exp.comp ((measurable_const.mul hTime).neg)
  have hPay : Measurable (fun ω : Ω => ENNReal.ofReal
      (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X upper ω))))) :=
    ENNReal.measurable_ofReal.comp hExp
  exact Measurable.ite hEvent hPay measurable_const
