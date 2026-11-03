-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_21_original_strict_survival_signed_cash_le_rightLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:57:27.547957+00:00
-- url     : https://prove2.me/submissions/2bf5f072-d3ee-4668-a7ce-b4c23c79f11b

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_pathwise_full_stieltjes_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_paymentTimes_strict_horizon_eq_Icc
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Same-domain signed original Stieltjes cash via W7-03 and already Proved closed-horizon cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (ω : Ω) (T : ℝ≥0)
    (hstrict : (T : ℝ≥0∞) < ruinTime X x D ω)
    (hRight : 0 ≤ rightLimit D T ω) :
    (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ≤
        rightLimit D T ω := by
  have hT : (0 : ℝ) ≤ (T : ℝ) := T.property
  have hconvert :=
    avram_wave7_03_original_real_horizon_pathwise_full_stieltjes_eq
      X x D hD ω (T : ℝ) hT q hq
  have hcash :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
          ENNReal.ofReal (rightLimit D T ω) := by
    rw [avram_wave8_21_original_paymentTimes_strict_horizon_eq_Icc
      (ruinTime X x D ω) T hstrict]
    exact avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
      q hq D hD ω T
  rw [hconvert] at hcash
  exact (ENNReal.ofReal_le_ofReal_iff hRight).mp hcash
