-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_esscher_stopped_mass_eq_original_two_sided_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T13:06:14.100571+00:00
-- url     : https://prove2.me/submissions/3e624f3a-2f8b-4237-815a-e6c0eb0e0466

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_exit_expectation_eq_restrict_lintegral
import Theorems.Thm_AvramDividend_Classical_upperPassage_measurable_from_stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine stopped Esscher record factor is exactly a scalar
multiple of the original strict two-sided exit expectation, for any
finite real rate p+q; no exit scale ratio is imported. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q p a x : ℝ) :
    (∫⁻ ω in {ω : Ω |
      twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω},
      ENNReal.ofReal (Real.exp (φ * (a - x) -
        (p + q) * (twoSidedExitUpTime X (a - x) ω).toReal)) ∂P) =
      ENNReal.ofReal (Real.exp (φ * (a - x))) *
        twoSidedExitExpectation X (p + q) a x := by
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (φ * (a - x)))
  have hUpper : Measurable (twoSidedExitUpTime X (a - x)) :=
    upperPassage_measurable_from_stopping X (a - x)
  have hf : Measurable (fun ω : Ω =>
      ENNReal.ofReal (Real.exp (-(p + q) *
        (twoSidedExitUpTime X (a - x) ω).toReal))) := by
    have hT : Measurable (fun ω : Ω =>
        (twoSidedExitUpTime X (a - x) ω).toReal) :=
      ENNReal.measurable_toReal.comp hUpper
    fun_prop
  have hFactor (ω : Ω) :
      ENNReal.ofReal (Real.exp (φ * (a - x) -
        (p + q) * (twoSidedExitUpTime X (a - x) ω).toReal)) =
      c * ENNReal.ofReal (Real.exp (-(p + q) *
        (twoSidedExitUpTime X (a - x) ω).toReal)) := by
    have hExp : Real.exp (φ * (a - x) -
        (p + q) * (twoSidedExitUpTime X (a - x) ω).toReal) =
        Real.exp (φ * (a - x)) *
          Real.exp (-(p + q) *
            (twoSidedExitUpTime X (a - x) ω).toReal) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hExp]
    simpa only [c] using
      (ENNReal.ofReal_mul (Real.exp_nonneg (φ * (a - x))) :
        ENNReal.ofReal (Real.exp (φ * (a - x)) *
          Real.exp (-(p + q) *
            (twoSidedExitUpTime X (a - x) ω).toReal)) =
        ENNReal.ofReal (Real.exp (φ * (a - x))) *
          ENNReal.ofReal (Real.exp (-(p + q) *
            (twoSidedExitUpTime X (a - x) ω).toReal)))
  calc
    _ = (∫⁻ ω in {ω : Ω |
        twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω},
        c * ENNReal.ofReal (Real.exp (-(p + q) *
          (twoSidedExitUpTime X (a - x) ω).toReal)) ∂P) := by
      apply lintegral_congr
      exact hFactor
    _ = c * (∫⁻ ω in {ω : Ω |
        twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω},
        ENNReal.ofReal (Real.exp (-(p + q) *
          (twoSidedExitUpTime X (a - x) ω).toReal)) ∂P) := by
      rw [lintegral_const_mul c hf]
    _ = c * twoSidedExitExpectation X (p + q) a x := by
      rw [avram_root29_03_exit_expectation_eq_restrict_lintegral]
      simp only [neg_mul]
