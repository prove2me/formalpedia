-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_zero_clock_masked_full_stieltjes_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T11:33:47.956835+00:00
-- url     : https://prove2.me/submissions/250d8762-3e15-46a6-800e-c3d20a372bd7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_cash_pointwise_le
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_zero_clock_real_cash_eq_initial_rightatom
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
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
    (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    (∫⁻ ω, if τ ω = 0 then
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≤
    (∫⁻ ω, if τ ω = 0 then ENNReal.ofReal (w x) else 0 ∂P) := by
  have hStrategy : IsDividendStrategy 𝓕 D := hD.1.1
  apply lintegral_mono
  intro ω
  by_cases hZero : τ ω = 0
  · simp only [if_pos hZero]
    have hD0 : D 0 ω = 0 := hStrategy.1 ω
    have hD0Nonneg : 0 ≤ D 0 ω := by simp [hD0]
    have hRightNonneg : 0 ≤ rightLimit D 0 ω :=
      le_trans hD0Nonneg
        (dividendStrategy_le_rightLimit D hStrategy ω 0)
    have hCashAtom :=
      avram_p4_d_dividend_original_zero_clock_real_cash_eq_initial_rightatom
        X x q D hStrategy τ Cash hCash ω hZero
    have hCashZero : Cash ω = rightLimit D 0 ω := by
      rw [hCashAtom, hD0, sub_zero, ENNReal.toReal_ofReal hRightNonneg]
    have hMass :
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) =
        ENNReal.ofReal (Cash ω) := by
      calc
        _ = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) := by
              simpa [hZero]
        _ = (dividendMeasure D ω) ({0} : Set ℝ) :=
              avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
                D ω (ruinTime X x D ω) q
        _ = ENNReal.ofReal (rightLimit D 0 ω - D 0 ω) :=
              dividendMeasure_singleton_eq_rightLimit_sub D hStrategy ω 0
        _ = ENNReal.ofReal (Cash ω) := by
              rw [hCashZero, hD0, sub_zero]
    rw [hMass]
    apply ENNReal.ofReal_le_ofReal
    exact avram_ubv_hor3_original_zero_clock_cash_pointwise_le
      X x q w C hw0 hw_cont hw_neg hw_smooth hw_grad hxc
      D hD hjump τ W Cash Term hW hCash hTerm ω hZero
  · simp [hZero]
