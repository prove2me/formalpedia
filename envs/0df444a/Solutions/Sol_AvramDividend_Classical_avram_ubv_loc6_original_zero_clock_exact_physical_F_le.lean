-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_original_zero_clock_exact_physical_F_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:34:43.710832+00:00
-- url     : https://prove2.me/submissions/b78fbac8-ee27-46e5-a92c-2de1bdb061d1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Retain the exact original stopped physical reward at the closed zero clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (k : ℕ) (ω : Ω) (hzero : σ k ω = 0) :
    F k ω ≤ w x := by
  classical
  let W : Ω → ℝ := fun ξ =>
    if σ k ξ = 0 ∨ (σ k ξ : ℝ≥0∞) < ruinTime X x D ξ then
      x + X.X (σ k ξ) ξ - rightLimit D (σ k ξ) ξ
    else riskProcess X x D (σ k ξ) ξ
  let Cash : Ω → ℝ := fun ξ =>
    (∫⁻ s in paymentTimes (ruinTime X x D ξ) ∩ Iic (σ k ξ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ξ)).toReal
  let Term : Ω → ℝ := fun ξ =>
    Real.exp (-(q * (σ k ξ : ℝ))) * w (W ξ)
  have hW : ∀ ξ, W ξ =
      if σ k ξ = 0 ∨ (σ k ξ : ℝ≥0∞) < ruinTime X x D ξ then
        x + X.X (σ k ξ) ξ - rightLimit D (σ k ξ) ξ
      else riskProcess X x D (σ k ξ) ξ := by
    intro ξ
    rfl
  have hCash : ∀ ξ, Cash ξ =
      (∫⁻ s in paymentTimes (ruinTime X x D ξ) ∩ Iic (σ k ξ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ξ)).toReal := by
    intro ξ
    rfl
  have hTerm : ∀ ξ, Term ξ =
      Real.exp (-(q * (σ k ξ : ℝ))) * w (W ξ) := by
    intro ξ
    rfl
  have hEq : F k ω = Term ω + Cash ω := by
    simpa only [Term, Cash, W] using hFsource k ω
  rw [hEq]
  exact avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
    X x q w C D hD hjump (σ k) W Cash Term
    hW hCash hTerm ω hzero
