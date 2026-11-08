-- Prove2me | solution 18 for AvramDividend.Classical.local_verification_uniform_strategy_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:10:06.911592+00:00
-- url     : https://prove2.me/submissions/d4aa829d-e6aa-4fda-8017-be4e8ca2111e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_dividendValue_le_bounded_variation
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_dividendValue_le_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_uniform_closed_cash_budget_implies_all_natural_stopped
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_dividendValue_eq_iSup_natural_ruin_stopped

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxC : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
  have hClosed : ∀ (T : ℝ), 0 ≤ T →
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by
    intro T hT
    by_cases hBV : X.BoundedVariation
    · exact admissible_cap_truncated_dividendValue_le_bounded_variation
        X hX hBV q hq w C hC hw_cont hw0 hw_neg (hw_smooth.2 hBV)
        hw_hjb x hx hxC D hD T hT
    · exact admissible_cap_truncated_dividendValue_le_unbounded_variation
        X hX hBV q hq w C hC hw_cont hw0 hw_neg (hw_smooth.1 hBV)
        hw_hjb x hx hxC D hD T hT
  have hNatural :=
    avram_limit2_original_uniform_closed_cash_budget_implies_all_natural_stopped
      X q x D (ENNReal.ofReal (w x)) hClosed
  rw [avram_wave6_10_original_dividendValue_eq_iSup_natural_ruin_stopped
    X q x D hD.1]
  exact iSup_le fun n => hNatural n
