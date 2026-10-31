-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_positive_ruin_expected_strict_stopped_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T11:18:23.780265+00:00
-- url     : https://prove2.me/submissions/07d6df28-157b-463f-b1fa-a8a20a47a244

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_positive_ruin_strict_stopped_drift_budget
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Expected full strict stopped dividends on the whole positive-ruin event
    have a deterministic finite-horizon budget, even if ruin is earlier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (H : ℝ≥0) (hH : 0 < H) :
    (∫⁻ ω, if 0 < ruinTime X x D ω then
      (∫⁻ r in paymentTimes
          (min (ruinTime X x D ω) (H : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * r)))
          ∂(dividendMeasure D ω)) else 0 ∂P) ≤
        ENNReal.ofReal (x + (H : ℝ) * X.drift) := by
  have hbound :=
    avram_wave3_03_bv_positive_ruin_strict_stopped_drift_budget
      X hX hBV x D hD q hq H hH
  calc
    _ ≤ ∫⁻ _ : Ω,
        ENNReal.ofReal (x + (H : ℝ) * X.drift) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hbound] with ω hω
      split_ifs with hruin
      · exact hω hruin
      · simp
    _ = ENNReal.ofReal (x + (H : ℝ) * X.drift) := by simp
