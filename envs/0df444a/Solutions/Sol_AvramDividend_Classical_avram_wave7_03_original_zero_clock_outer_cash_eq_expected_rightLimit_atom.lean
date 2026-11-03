-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_zero_clock_outer_cash_eq_expected_rightLimit_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:50:32.838338+00:00
-- url     : https://prove2.me/submissions/8cb6fc9c-b11c-4b4d-bf17-3a4283f7845f

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


/-- The actual original double ENNReal payout at time zero is exactly
    the expectation of the original Stieltjes right-limit dividend atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    ∫⁻ ω, ENNReal.ofReal (rightLimit D 0 ω) ∂P := by
  calc
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
      ∫⁻ ω, (dividendMeasure D ω) ({0} : Set ℝ) ∂P := by
        apply lintegral_congr
        intro ω
        exact avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
          D ω (ruinTime X x D ω) q
    _ = ∫⁻ ω, ENNReal.ofReal (rightLimit D 0 ω) ∂P := by
        apply lintegral_congr
        intro ω
        have hAtom :=
          avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
            D hD ω 0
        simpa using hAtom
