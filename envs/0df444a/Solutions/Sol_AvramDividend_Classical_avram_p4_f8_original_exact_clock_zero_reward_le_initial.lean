-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f8_original_exact_clock_zero_reward_le_initial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:18:56.524685+00:00
-- url     : https://prove2.me/submissions/77777181-e474-482a-910c-22cd08a9eaea

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

/-- The authentic original source's closed dividend atom and postpayment
terminal sum cannot exceed w(x) at a zero stopping clock. -/
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
        ∂(dividendMeasure D ω)).toReal) :
    ∀ k ω, σ k ω = 0 → F k ω ≤ w x := by
  intro k ω hzero
  let W : Ω → ℝ := fun η =>
    if σ k η = 0 ∨ (σ k η : ℝ≥0∞) < ruinTime X x D η then
      x + X.X (σ k η) η - rightLimit D (σ k η) η
    else riskProcess X x D (σ k η) η
  let Cash : Ω → ℝ := fun η =>
    (∫⁻ s in paymentTimes (ruinTime X x D η) ∩ Iic (σ k η : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D η)).toReal
  let Term : Ω → ℝ := fun η =>
    Real.exp (-(q * (σ k η : ℝ))) * w (W η)
  have hbound : Term ω + Cash ω ≤ w x :=
    avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
      X x q w C D hD hjump (σ k) W Cash Term
      (by intro η; rfl) (by intro η; rfl) (by intro η; rfl)
      ω hzero
  have hreward : F k ω = Term ω + Cash ω := by
    simpa only [Term, Cash, W] using hFsource k ω
  rw [hreward]
  exact hbound
