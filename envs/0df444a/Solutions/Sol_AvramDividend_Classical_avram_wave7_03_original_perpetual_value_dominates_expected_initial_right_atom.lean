-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_perpetual_value_dominates_expected_initial_right_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:58:20.910626+00:00
-- url     : https://prove2.me/submissions/e37f0806-0164-437a-b12b-bc87caa8623b

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The actual source perpetual expected dividend cash always contains
    the complete original time-zero right-limit Stieltjes atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (rightLimit D 0 ω) ∂P) ≤
      dividendValue X q x D := by
  have hZero (ω : Ω) :
      ENNReal.ofReal (rightLimit D 0 ω) =
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)) := by
    calc
      ENNReal.ofReal (rightLimit D 0 ω) =
        (dividendMeasure D ω) ({0} : Set ℝ) := by
          have hAtom :=
            avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
              D hD ω 0
          simpa using hAtom.symm
      _ = (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)) :=
        (avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
          D ω (ruinTime X x D ω) q).symm
  calc
    (∫⁻ ω, ENNReal.ofReal (rightLimit D 0 ω) ∂P) =
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) := by
            apply lintegral_congr
            intro ω
            exact hZero ω
    _ ≤ dividendValue X q x D := by
      change (∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤
        (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P)
      apply lintegral_mono
      intro ω
      exact lintegral_mono_set Set.inter_subset_left
