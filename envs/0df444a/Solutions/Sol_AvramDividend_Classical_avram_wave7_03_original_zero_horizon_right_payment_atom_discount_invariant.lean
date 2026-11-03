-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_zero_horizon_right_payment_atom_discount_invariant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:38:54.826103+00:00
-- url     : https://prove2.me/submissions/b6c31e35-11d9-417a-b15c-b2408bd5d85b

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The complete original right-payment atom at time zero is invariant
    under any change of discount rate, including immediate ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (q₁ q₂ : ℝ) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q₁ * t)))
        ∂(dividendMeasure D ω)) =
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q₂ * t)))
        ∂(dividendMeasure D ω)) := by
  calc
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q₁ * t)))
        ∂(dividendMeasure D ω)) =
      (dividendMeasure D ω) ({0} : Set ℝ) :=
        avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
          D ω (ruinTime X x D ω) q₁
    _ =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q₂ * t)))
          ∂(dividendMeasure D ω)) :=
        (avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
          D ω (ruinTime X x D ω) q₂).symm
