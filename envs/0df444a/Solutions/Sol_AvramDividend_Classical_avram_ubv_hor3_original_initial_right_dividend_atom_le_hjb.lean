-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_initial_right_dividend_atom_le_hjb
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:28:48.768124+00:00
-- url     : https://prove2.me/submissions/699f12b7-1af2-476a-9561-9bae9465ffd2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_cash_pointwise_le
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_zero_clock_real_cash_eq_initial_rightatom
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
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
    (ω : Ω) :
    (dividendMeasure D ω) ({0} : Set ℝ) ≤ ENNReal.ofReal (w x) := by
  let τ : Ω → ℝ≥0 := fun _ => 0
  let W : Ω → ℝ := fun ζ => x + X.X 0 ζ - rightLimit D 0 ζ
  let Cash : Ω → ℝ := fun ζ =>
    (∫⁻ s in paymentTimes (ruinTime X x D ζ) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ζ)).toReal
  let Term : Ω → ℝ := fun ζ => w (W ζ)
  have hW : ∀ ζ, W ζ =
      if τ ζ = 0 ∨ (τ ζ : ℝ≥0∞) < ruinTime X x D ζ
      then x + X.X (τ ζ) ζ - rightLimit D (τ ζ) ζ
      else riskProcess X x D (τ ζ) ζ := by
    intro ζ
    simp [W, τ]
  have hCash : ∀ ζ, Cash ζ =
      (∫⁻ s in paymentTimes (ruinTime X x D ζ) ∩ Iic (τ ζ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ζ)).toReal := by
    intro ζ
    rfl
  have hTerm : ∀ ζ, Term ζ =
      Real.exp (-(q * (τ ζ : ℝ))) * w (W ζ) := by
    intro ζ
    simp [Term, τ]
  have hCashBound : Cash ω ≤ w x :=
    avram_ubv_hor3_original_zero_clock_cash_pointwise_le
      X x q w C hw0 hw_cont hw_neg hw_smooth hw_grad hxc
      D hD hjump τ W Cash Term hW hCash hTerm ω rfl
  have hStrategy : IsDividendStrategy 𝓕 D := hD.1.1
  have hD0 : D 0 ω = 0 := hStrategy.1 ω
  have hD0Nonneg : 0 ≤ D 0 ω := by simp [hD0]
  have hRightNonneg : 0 ≤ rightLimit D 0 ω :=
    le_trans hD0Nonneg
      (dividendStrategy_le_rightLimit D hStrategy ω 0)
  have hCashAtom :=
    avram_p4_d_dividend_original_zero_clock_real_cash_eq_initial_rightatom
      X x q D hStrategy τ Cash hCash ω rfl
  have hCashZero : Cash ω = rightLimit D 0 ω := by
    rw [hCashAtom, hD0, sub_zero, ENNReal.toReal_ofReal hRightNonneg]
  calc
    (dividendMeasure D ω) ({0} : Set ℝ) =
        ENNReal.ofReal (rightLimit D 0 ω - D 0 ω) :=
      dividendMeasure_singleton_eq_rightLimit_sub D hStrategy ω 0
    _ = ENNReal.ofReal (Cash ω) := by rw [hCashZero, hD0, sub_zero]
    _ ≤ ENNReal.ofReal (w x) := ENNReal.ofReal_le_ofReal hCashBound
