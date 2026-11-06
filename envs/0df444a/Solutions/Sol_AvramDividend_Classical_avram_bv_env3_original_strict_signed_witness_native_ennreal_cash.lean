-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_original_strict_signed_witness_native_ennreal_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T11:54:54.93967+00:00
-- url     : https://prove2.me/submissions/cf25577f-359e-4899-80ff-3d0f5eab55a8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_strict_HJB_to_signed_full
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_any_clock_strict_survival_terminal_max_eq_signed
import Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_deterministic_horizon_real_cash_budget_to_ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) (M B : Ω → ℝ)
    (hMint : Integrable M P) (hBint : Integrable B P)
    (hSigned : (∫ ω, M ω + B ω ∂P) ≤ 0)
    (hWitness : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T, ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if ENNReal.ofNNReal (⟨T, hT⟩ : ℝ≥0) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D ⟨T, hT⟩ ω)
       else 0) ≤ w x + M ω + B ω) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let S : ℝ≥0 := ⟨T, hT⟩
  let Y : Ω → ℝ := fun ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
    ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  have hYI : Integrable Y P := avram_p3_bv_original_prebudget_L1 X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq) T hT
  have hDomI : Integrable (fun ω => w x + M ω + B ω) P := ((integrable_const (w x)).add hMint).add hBint
  have hYLe : ∀ᵐ ω ∂P, Y ω ≤ w x + M ω + B ω := by
    filter_upwards [hWitness] with ω hω
    simpa only [Y, S] using hω
  have hDomMean : (∫ ω, w x + M ω + B ω ∂P) =
      w x + (∫ ω, M ω + B ω ∂P) := by
    calc
      _ = (∫ ω, w x + (M ω + B ω) ∂P) := by congr 1; funext ω; ring
      _ = (∫ ω, w x ∂P) + (∫ ω, M ω + B ω ∂P) :=
        integral_add (integrable_const (w x)) (hMint.add hBint)
      _ = _ := by simp
  have hStrict : (∫ ω, Y ω ∂P) ≤ w x := by
    calc
      _ ≤ (∫ ω, w x + M ω + B ω ∂P) := integral_mono_ae hYI hDomI hYLe
      _ = w x + (∫ ω, M ω + B ω ∂P) := hDomMean
      _ ≤ w x := by linarith only [hSigned]
  have hFull := avram_p3_bv_strict_HJB_to_signed_full
    X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_grad x D hD hjump T hT hTpos hStrict
  have hTermNN : ∀ ω, 0 ≤ (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω) else 0) := by
    intro ω
    have hEq := avram_wave8_04_original_BV_any_clock_strict_survival_terminal_max_eq_signed
      X q w C hC hw_cont hw0 hw_smooth hw_grad x hxc D hD (fun _ => S) ω
    change (if (S : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω))
      else 0) = (if (S : ℝ≥0∞) < ruinTime X x D ω then Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω) else 0) at hEq
    rw [← hEq]
    split_ifs
    · exact le_max_left _ _
    · exact le_refl _
  have hTermMeanNN : 0 ≤ (∫ ω, if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω) else 0 ∂P) := integral_nonneg hTermNN
  have hRealCash : (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) ≤ w x := by linarith only [hFull, hTermMeanNN]
  exact avram_chat07b_original_deterministic_horizon_real_cash_budget_to_ENNReal
    X x C D hD q T (w x) hT hRealCash
