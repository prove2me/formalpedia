-- Prove2me | solution 1 for AvramDividend.Classical.chat04_lower_exit_discounted_creeping_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:03:59.604996+00:00
-- url     : https://prove2.me/submissions/01ebe666-b276-480a-bc8f-cb712a53daeb

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_scale_creeping_atom

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
The lower-exit scale payoff factors through the discounted mass of exact contact
at reserve zero. No absence-of-creeping or zero-origin hypothesis is assumed.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) :
    (∫⁻ ω,
      if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitDownTime X (-x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0 ∂P) =
      (∫⁻ ω,
        if twoSidedExitDownTime X (-x) ω <
            twoSidedExitUpTime X (a - x) ω ∧
           x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω = 0
        then ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitDownTime X (-x) ω).toReal)))
        else 0 ∂P) * ENNReal.ofReal (W 0) := by
  calc
    (∫⁻ ω,
      if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitDownTime X (-x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0 ∂P) =
      (∫⁻ ω,
        (if twoSidedExitDownTime X (-x) ω <
             twoSidedExitUpTime X (a - x) ω ∧
            x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω = 0
         then ENNReal.ofReal (Real.exp (-(q *
           (twoSidedExitDownTime X (-x) ω).toReal)))
         else 0) * ENNReal.ofReal (W 0) ∂P) := by
      apply lintegral_congr
      intro ω
      rw [AvramDividend.Classical.chat04_lower_exit_scale_creeping_atom
        X q W hW a x ω]
      by_cases h : twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω
      · by_cases hz :
          x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω = 0
        · simp [h, hz]
        · simp [h, hz]
      · simp [h]
    _ = _ := by
      exact lintegral_mul_const'
        (ENNReal.ofReal (W 0))
        (fun ω : Ω =>
          if twoSidedExitDownTime X (-x) ω <
              twoSidedExitUpTime X (a - x) ω ∧
             x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω = 0
          then ENNReal.ofReal (Real.exp (-(q *
            (twoSidedExitDownTime X (-x) ω).toReal)))
          else 0)
        ENNReal.ofReal_ne_top
