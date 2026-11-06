-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit1_bv_direct_postpayment_terminal_to_dividendValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:56:24.285954+00:00
-- url     : https://prove2.me/submissions/47907e7b-fef0-4c94-93a9-9f329779924f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_terminal_integrable_mean_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_ennreal_fibre_toReal_mean_eq_signed_stieltjes_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The actual BV postpayment terminal is integrable and nonnegative,
    and all positive stopped HJB budgets pass to the perpetual cash value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (B : ℝ)
    (hBudget : ∀ (T : ℝ) (hT : 0 ≤ T), 0 < T →
      let S : ℝ≥0 := ⟨T, hT⟩
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0) ∂P) ≤ B) :
    (∀ (T : ℝ) (hT : 0 ≤ T), 0 < T →
      let S : ℝ≥0 := ⟨T, hT⟩
      Integrable (fun ω => (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0)) P) ∧
    dividendValue X q x D ≤ ENNReal.ofReal B := by
  constructor
  · intro T hT hTpos
    exact (avram_wave8_04_original_BV_positive_horizon_signed_terminal_integrable_mean_eq
      X hBV q w C hC hw_cont hw0 hw_neg hw_smooth hw_grad x D hD
      T hT hTpos).1
  · apply avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le
      X x C D hD q hq B
    intro n
    let T : ℝ := (((n + 1 : ℕ) : ℝ))
    have hT : 0 ≤ T := by dsimp [T]; positivity
    have hTpos : 0 < T := by dsimp [T]; positivity
    let S : ℝ≥0 := ⟨T, hT⟩
    have hTermPoint (ω : Ω) : 0 ≤ (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0) := by
      by_cases hBefore : (S : ℝ≥0∞) < ruinTime X x D ω
      · have hPost := avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
          X w C hC hw0 hw_cont hw_neg hw_smooth hw_grad x hx hxc D hD ω S
        have hExp : (0 : ℝ) ≤ Real.exp (-(q * T)) := Real.exp_nonneg _
        simpa only [if_pos hBefore] using mul_nonneg hExp hPost
      · simp [hBefore]
    have hTermAE : ∀ᵐ ω ∂P, 0 ≤ (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0) :=
      Filter.Eventually.of_forall hTermPoint
    have hTermMean : (0 : ℝ) ≤
        (∫ ω, (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0) ∂P) :=
      integral_nonneg_of_ae hTermAE
    have hCashEq :=
      avram_wave7_03_original_real_horizon_ennreal_fibre_toReal_mean_eq_signed_stieltjes_mean
        X x D hD.1.1 q hq T hT
    have hJoint := hBudget T hT hTpos
    change (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0) ∂P) ≤ B at hJoint
    rw [hCashEq] at hJoint
    have hMean : (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B := by
      linarith only [hJoint, hTermMean]
    simpa only [T] using hMean
