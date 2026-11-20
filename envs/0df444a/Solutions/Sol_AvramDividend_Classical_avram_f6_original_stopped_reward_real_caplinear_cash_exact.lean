-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_stopped_reward_real_caplinear_cash_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:55:26.324478+00:00
-- url     : https://prove2.me/submissions/d44ad967-219c-4349-98d7-44a2ebcaa47a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_stopped_reward_caplinear_cash_exact
import Theorems.Thm_AvramDividend_Classical_avram_f6_caplinear_ofReal_real_switch_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ k ω,
      let V : ℝ → ℝ := fun z =>
        if C = ⊤ then w z
        else if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal)
      let W : ℝ := if σ k ω = 0 ∨
          (σ k ω : ℝ≥0∞) < ruinTime X x D ω
        then x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
        else riskProcess X x D (σ k ω) ω
      F k ω = Real.exp (-(q * (σ k ω : ℝ))) * V W +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by
  intro k ω
  have h :=
    avram_f6_original_stopped_reward_caplinear_cash_exact
      X x C hC hxc w D hD q σ F hFsource k ω
  dsimp at h ⊢
  simpa only [avram_f6_caplinear_ofReal_real_switch_exact C hC w] using h
