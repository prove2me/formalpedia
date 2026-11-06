-- Prove2me | solution 5 for AvramDividend.Classical.avram_wave8_04_original_BV_positive_time_complete_stieltjes_supermartingale
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:20:35.851258+00:00
-- url     : https://prove2.me/submissions/6802075a-bc91-4f65-8b5f-57f2285ac41c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_stopped_HJB_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_positive_horizon_strict_survival_terminal_max_eq_signed
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_bounded_random_clock_signed_postterminal_L1
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
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T,hT⟩
    let Term : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω))
      else 0
    Integrable Term P ∧
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
        (∫ ω, Term ω ∂P) ≤ w x := by
  let S : ℝ≥0 := ⟨T, hT⟩
  have hStoReal : (S : ℝ) = T := rfl
  let Signed : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) *
        w (x + X.X S ω - rightLimit D S ω)
    else 0
  let Term : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * T)) *
        w (x + X.X S ω - rightLimit D S ω))
    else 0
  have hEq : Term = Signed := by
    funext ω
    exact avram_wave8_04_positive_horizon_strict_survival_terminal_max_eq_signed
      X q w C hC hw_cont hw0 hw_smooth hw_grad x D hD T hT hTpos ω
  have hSignedInt : Integrable Signed P := by
    dsimp [Signed]
    simpa only [hStoReal] using
      (avram_p3_g2_original_bounded_random_clock_signed_postterminal_L1
        X hX hBV q hq w hw_cont hw0 hw_neg C hC hw_smooth hw_grad
        x hxc D hD S (fun _ => S) measurable_const (by intro ω; exact le_rfl))
  have hSignedBudget :
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
        (∫ ω, Signed ω ∂P) ≤ w x := by
    simpa [Signed, S] using
      (avram_wave8_04_original_BV_positive_horizon_signed_stopped_HJB_budget
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
        hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos)
  change Integrable Term P ∧
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, Term ω ∂P) ≤ w x
  constructor
  · simpa only [hEq] using hSignedInt
  · simpa only [hEq] using hSignedBudget
