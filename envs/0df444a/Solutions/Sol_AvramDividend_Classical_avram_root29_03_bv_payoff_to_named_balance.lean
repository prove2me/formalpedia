-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_bv_payoff_to_named_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:42:34.323192+00:00
-- url     : https://prove2.me/submissions/fd1a8b60-331c-4fd4-80c8-50ef33a03fd4

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_exact_upperfirst_discount_integrand_measurable

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The exact BV original strict upper-exit payoff balance (09ca) implies
the named discounted upper-before-ruin expectation times scale W(a), using
a genuine measurable discount and an ENNReal lintegral constant factor. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hBVPayoff :
      (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
        ENNReal.ofReal (W a)
      else 0 ∂P) = ENNReal.ofReal (W x)) :
    twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by
  have hm : Measurable (fun ω : Ω =>
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (twoSidedExitUpTime X (a - x) ω))))
      else 0) :=
    chat03_exact_upperfirst_discount_integrand_measurable X (-x) (a - x) q
  calc
    twoSidedExitExpectation X q a x * ENNReal.ofReal (W a)
        = (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
            twoSidedExitDownTime X (-x) ω then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (twoSidedExitUpTime X (a - x) ω))))
          else 0 ∂P) * ENNReal.ofReal (W a) := rfl
    _ = (∫⁻ ω, (if twoSidedExitUpTime X (a - x) ω <
              twoSidedExitDownTime X (-x) ω then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (twoSidedExitUpTime X (a - x) ω))))
          else 0) * ENNReal.ofReal (W a) ∂P) := by
      rw [lintegral_mul_const _ hm]
    _ = (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
            twoSidedExitDownTime X (-x) ω then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal (W a)
          else 0 ∂P) := by
      apply lintegral_congr
      intro ω
      simp only [ite_mul, zero_mul]
    _ = ENNReal.ofReal (W x) := hBVPayoff
