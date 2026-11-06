-- Prove2me | solution 5 for AvramDividend.Classical.avram_wave6_chat05_bv_drift_envelope_complement_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:22:53.355617+00:00
-- url     : https://prove2.me/submissions/b6a71fe1-387e-4a00-9630-8390bf524d82
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_source_signed_fatou_grid_certificate
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_signed_full_from_Fatou_mesh
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_initial_value_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_any_clock_strict_survival_terminal_max_eq_signed
import Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_deterministic_horizon_real_cash_budget_to_ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T)
    (hEnvelope : ¬ (x + T * X.drift ≤ w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  classical
  let S : ℝ≥0 := ⟨T, hT⟩
  let Term : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω)
    else 0
  have hTpos := (avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
    X hX hBV q hq w C hC hw_cont hw0 hw_smooth hw_grad
    x hx hxc D hD T hT hEnvelope).1
  have hwx := avram_p3_bv_initial_value_nonnegative
    C hC w hw_cont hw0 hw_smooth hw_grad x hx hxc
  obtain ⟨F, M, B, hFm, hFi, hFn, hSigned, hMesh, hLiminf⟩ :=
    avram_p3_bv_original_source_signed_fatou_grid_certificate
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos
  have hClosed := avram_p3_bv_signed_full_from_Fatou_mesh
    X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
    x hwx D hD hw_nonneg hjump T hT hTpos
    F M B hFm hFi hFn hSigned hMesh hLiminf
  have hTermNonneg : ∀ ω, 0 ≤ Term ω := by
    intro ω
    have hEq := avram_wave8_04_original_BV_any_clock_strict_survival_terminal_max_eq_signed
      X q w C hC hw_cont hw0 hw_smooth hw_grad x hxc D hD (fun _ => S) ω
    change (if (S : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω))
      else 0) = Term ω at hEq
    rw [← hEq]
    split_ifs
    · exact le_max_left _ _
    · exact le_refl _
  have hTermMean : 0 ≤ (∫ ω, Term ω ∂P) := integral_nonneg hTermNonneg
  have hReal : (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) ≤ w x := by
    change (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, Term ω ∂P) ≤ w x at hClosed
    linarith only [hClosed, hTermMean]
  exact avram_chat07b_original_deterministic_horizon_real_cash_budget_to_ENNReal
    X x C D hD q T (w x) hT hReal
