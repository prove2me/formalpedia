-- Prove2me | solution 30 for AvramDividend.Classical.admissible_cap_truncated_dividendValue_le_bounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:15:16.583208+00:00
-- url     : https://prove2.me/submissions/76f5abdb-0ab8-4c60-8fee-c47f12ba48dd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_corrected_positive_cap_bv_parent_zero_horizon_full_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_full_cash_and_survival_terminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_terminal_integrable_mean_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_stopped_HJB_budget
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_bv_real_terminal_budget_to_closed_ennreal
import Theorems.Thm_AvramDividend_Classical_avram_sweep18_original_BV_HJB_stopping_criteria
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  rcases avram_sweep18_original_BV_HJB_stopping_criteria
    X hBV q w C hC hw_cont hw0 hw_smooth hw_hjb x hx hxc D hD
    with ⟨hwGen, hwGrad, hwNonneg, hwJump⟩
  rcases eq_or_lt_of_le hT with hTzero | hTpos
  · subst T
    exact avram_wave7_09_corrected_positive_cap_bv_parent_zero_horizon_full_stieltjes_bound
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hwGen hwGrad x hxc D hD hwNonneg
  · let S : ℝ≥0 := ⟨T, hT⟩
    let Term : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω))
      else 0
    have hL1 := avram_wave8_04_original_BV_full_cash_and_survival_terminal_L1
      X hBV q w hw_cont hw_neg x C D hD T hT
    have hMean := avram_wave8_04_original_BV_positive_horizon_signed_terminal_integrable_mean_eq
      X hBV q w C hC hw_cont hw0 hw_neg hw_smooth hwGrad x D hD T hT hTpos
    have hSigned := avram_wave8_04_original_BV_positive_horizon_signed_stopped_HJB_budget
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hwGen hwGrad x hx hxc D hD hwNonneg hwJump T hT hTpos
    have hSM : Integrable Term P ∧ (∫ ω, (∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
        (∫ ω, Term ω ∂P) ≤ w x := by
      refine ⟨hL1.2, ?_⟩
      rw [← hMean.2]; exact hSigned
    have hTermNN : ∀ ω, 0 ≤ Term ω := by intro ω; dsimp [Term]; split_ifs <;> positivity
    exact avram_sweep16_bv_real_terminal_budget_to_closed_ennreal
      X x C D hD q (le_of_lt hq) T hT (w x) Term
      (by simpa only [S, Term] using hSM.1)
      hTermNN
      (by simpa only [S, Term] using hSM.2)
