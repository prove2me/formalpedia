-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_original_time_truncation_eventually_exact_closed_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:52:49.986312+00:00
-- url     : https://prove2.me/submissions/4e1bfff8-141e-47c8-92d4-39f7aa1385a0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_bounded_clock_min_nat_stopping_and_exact_payoff_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Natural stopping-clock truncations eventually agree with the exact closed-clock payoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (n : ℕ)
    (hBound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (σ : ℕ → Ω → ℝ≥0)
    (hσeq : ∀ k ω, σ k ω = min (τ ω) (k : ℝ≥0))
    (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ ω, ∀ᶠ k : ℕ in Filter.atTop, F k ω = Term ω + Cash ω := by
  classical
  let Pay : ℝ≥0 → Ω → ℝ := fun s ω =>
    Real.exp (-(q * (s : ℝ))) *
      w (if s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X s ω - rightLimit D s ω
      else riskProcess X x D s ω) +
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (s : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)).toReal
  obtain ⟨_, _, hEvent, _⟩ :=
    avram_ubv_loc6_bounded_clock_min_nat_stopping_and_exact_payoff_limit
      (𝓕 := 𝓕.rightCont) τ n hBound hτstop Pay
  intro ω
  filter_upwards [hEvent ω] with k hk
  have hs : σ k ω = τ ω := by rw [hσeq]; exact hk
  rw [hFsource k ω, hs, hTerm ω, hCash ω, hW ω]
