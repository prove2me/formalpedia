-- Prove2me | solution 9 for AvramDividend.Classical.admissible_cap_truncated_bv_stochastic_core_positive_cap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T09:00:08.914506+00:00
-- url     : https://prove2.me/submissions/9df28075-0589-492b-9607-44a9542176a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_corrected_positive_cap_bv_parent_zero_horizon_full_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_time_complete_stieltjes_supermartingale
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_bounded_random_clock_toReal_budget_to_ennreal_cash
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
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  rcases eq_or_lt_of_le hT with hZero | hTpos
  · subst T
    exact
      avram_wave7_09_corrected_positive_cap_bv_parent_zero_horizon_full_stieltjes_bound
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_gen hw_grad x hxc D hD hw_nonneg
  · let S : ℝ≥0 := ⟨T, hT⟩
    have hCore :=
      avram_wave8_04_original_BV_positive_time_complete_stieltjes_supermartingale
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos
    dsimp only at hCore
    have hNonneg :
        0 ≤ ∫ ω, (if (S : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * T)) *
            w (x + X.X S ω - rightLimit D S ω)) else 0) ∂P := by
      apply integral_nonneg
      intro ω
      by_cases hsurv : (S : ℝ≥0∞) < ruinTime X x D ω
      all_goals simp [hsurv]
    have hBudget :
        (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal ∂P) ≤ w x := by
      linarith [hCore.2, hNonneg]
    have hBound :=
      avram_wave7_03_original_bounded_random_clock_toReal_budget_to_ennreal_cash
        X x C D hD q (le_of_lt hq) S
        (fun _ : Ω => S)
        (by intro ω; exact le_rfl)
        (by exact measurable_const)
        (w x) hBudget
    exact hBound
