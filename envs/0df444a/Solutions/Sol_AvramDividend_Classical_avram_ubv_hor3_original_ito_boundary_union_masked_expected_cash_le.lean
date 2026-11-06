-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_ito_boundary_union_masked_expected_cash_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:15:52.29469+00:00
-- url     : https://prove2.me/submissions/f71e53bc-683d-4280-b765-c416e173af86

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_ito_boundary_union_pointwise_cash_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, if n = 0 ∨ T = 0 ∨ ruinTime X x D ω = 0 then
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≤
    (∫⁻ ω, if n = 0 ∨ T = 0 ∨ ruinTime X x D ω = 0 then
      ENNReal.ofReal (w x) else 0 ∂P) := by
  apply lintegral_mono
  intro ω
  by_cases hBoundary : n = 0 ∨ T = 0 ∨ ruinTime X x D ω = 0
  · have hPoint :=
      avram_ubv_hor3_original_ito_boundary_union_pointwise_cash_le
        X x q w C hw0 hw_cont hw_neg hw_smooth hw_grad hxc D hD hjump
        n T hT ω hBoundary
    simpa only [hBoundary, ↓reduceIte] using hPoint
  · simp only [hBoundary, ↓reduceIte, le_rfl]
