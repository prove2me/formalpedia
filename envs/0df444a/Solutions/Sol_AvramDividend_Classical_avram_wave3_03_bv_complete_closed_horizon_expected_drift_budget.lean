-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_complete_closed_horizon_expected_drift_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:36:33.592031+00:00
-- url     : https://prove2.me/submissions/f12ece9b-748a-4ba5-afc6-683efe389ba1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_positive_ruin_closed_horizon_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_instant_ruin_closed_horizon_initial_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- For every capped admissible strategy, the entire original BV dividend
    Stieltjes reward through a closed horizon has finite expected drift budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T H : ℝ≥0) (hTH : T < H) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (x + (H : ℝ) * X.drift) := by
  have hdrift : 0 ≤ X.drift := (bv_standing_drift_pos X hX hBV).1.le
  have hposbudget := avram_wave3_03_bv_positive_ruin_closed_horizon_budget
    X hX hBV x D hD.1.1 q hq T H hTH
  have hpoint : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) ≤
        ENNReal.ofReal (x + (H : ℝ) * X.drift) := by
    filter_upwards [hposbudget] with ω hpositive
    rcases eq_or_lt_of_le
      (show (0 : ℝ≥0∞) ≤ ruinTime X x D ω from zero_le) with hzero | hpos
    · have hstart :=
        avram_wave3_03_bv_instant_ruin_closed_horizon_initial_budget
          X x C hxc D hD q T ω hzero.symm
      exact hstart.trans (ENNReal.ofReal_le_ofReal (by
        have hH : 0 ≤ (H : ℝ) := NNReal.coe_nonneg H
        nlinarith [mul_nonneg hH hdrift]))
    · exact hpositive hpos
  letI : IsProbabilityMeasure P := X.isProbability
  calc
    _ ≤ ∫⁻ _ : Ω, ENNReal.ofReal (x + (H : ℝ) * X.drift) ∂P :=
      lintegral_mono_ae hpoint
    _ = ENNReal.ofReal (x + (H : ℝ) * X.drift) := by simp
