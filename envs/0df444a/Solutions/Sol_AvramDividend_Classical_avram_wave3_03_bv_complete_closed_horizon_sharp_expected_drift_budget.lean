-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_complete_closed_horizon_sharp_expected_drift_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:54:25.396434+00:00
-- url     : https://prove2.me/submissions/c4f1bae8-62aa-487a-aec1-9516e335135d

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_complete_closed_horizon_expected_drift_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_ennreal_drift_budget_strict_horizon_to_closed

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The exact original BV complete dividend Stieltjes expectation is bounded
    by initial capital plus physical drift times its actual closed horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (x + (T : ℝ) * X.drift) := by
  have hd : 0 ≤ X.drift := (bv_standing_drift_pos X hX hBV).1.le
  let a : ℝ≥0 := ⟨x, hx⟩
  let d : ℝ≥0 := ⟨X.drift, hd⟩
  have hcast (H : ℝ≥0) :
      ENNReal.ofReal (x + (H : ℝ) * X.drift) =
        ((a + H * d : ℝ≥0) : ℝ≥0∞) := by
    have hreal : x + (H : ℝ) * X.drift = ((a + H * d : ℝ≥0) : ℝ) := by
      simp only [NNReal.coe_add, NNReal.coe_mul]
      rfl
    rw [hreal]
    exact ENNReal.ofReal_coe_nnreal
  rw [hcast T]
  apply avram_wave3_03_ennreal_drift_budget_strict_horizon_to_closed
  intro H hH
  have hbound := avram_wave3_03_bv_complete_closed_horizon_expected_drift_budget
    X hX hBV x hx C hxc D hD q hq T H hH
  simpa only [hcast H] using hbound
