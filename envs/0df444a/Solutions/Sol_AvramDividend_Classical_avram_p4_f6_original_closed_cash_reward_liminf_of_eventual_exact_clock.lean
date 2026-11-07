-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_original_closed_cash_reward_liminf_of_eventual_exact_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:19:46.821754+00:00
-- url     : https://prove2.me/submissions/2708382c-b21b-4b13-9118-9581b0346b4b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Once the genuine stopped clocks are eventually identical, the full
original closed-dividend payoff is eventually identical including atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
        else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hcofinal : ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, σ k ω = τ ω) :
    ∀ᵐ ω ∂P, ENNReal.ofReal (Term ω + Cash ω) =
      Filter.liminf (fun k => ENNReal.ofReal (F k ω)) atTop := by
  filter_upwards [hcofinal] with ω hω
  have hReward : ∀ᶠ k : ℕ in atTop, F k ω = Term ω + Cash ω := by
    filter_upwards [hω] with k hk
    rw [hFsource k ω, hk, hTerm ω, hW ω, hCash ω]
  have hEr : ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal (F k ω) = ENNReal.ofReal (Term ω + Cash ω) :=
    hReward.mono (fun k hk => congrArg ENNReal.ofReal hk)
  calc
    ENNReal.ofReal (Term ω + Cash ω) =
        Filter.liminf (fun _ : ℕ => ENNReal.ofReal (Term ω + Cash ω)) atTop := by
      rw [Filter.liminf_const]
    _ = Filter.liminf (fun k => ENNReal.ofReal (F k ω)) atTop :=
      (Filter.liminf_congr hEr).symm
