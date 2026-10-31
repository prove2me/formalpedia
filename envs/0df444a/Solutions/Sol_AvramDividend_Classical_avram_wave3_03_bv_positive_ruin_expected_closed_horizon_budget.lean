-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_positive_ruin_expected_closed_horizon_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:32:39.812772+00:00
-- url     : https://prove2.me/submissions/25ce234e-94fb-4b2e-bd6e-28ef249e0b61

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_positive_ruin_closed_horizon_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Expected complete closed-horizon BV dividend rewards, including the
    terminal atom and paths that ruin earlier, obey the original drift budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (T H : ℝ≥0) (hTH : T < H) :
    (∫⁻ ω, if 0 < ruinTime X x D ω then
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) else 0 ∂P) ≤
        ENNReal.ofReal (x + (H : ℝ) * X.drift) := by
  have hbound := avram_wave3_03_bv_positive_ruin_closed_horizon_budget
    X hX hBV x D hD q hq T H hTH
  calc
    _ ≤ ∫⁻ _ : Ω, ENNReal.ofReal (x + (H : ℝ) * X.drift) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hbound] with ω hω
      split_ifs with hruin
      · exact hω hruin
      · simp
    _ = ENNReal.ofReal (x + (H : ℝ) * X.drift) := by simp
