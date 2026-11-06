-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_original_cofinal_clock_payoff_eventually_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:23:52.515166+00:00
-- url     : https://prove2.me/submissions/d1a4fdb0-ca68-475f-80e6-af49a4b11ae7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- On every original-path cofinal spatial localisation, the bounded ruin
clock and its right-limit reserve, closed Stieltjes cash, and terminal reward
become literally equal to their natural-clock counterparts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (n : ℕ)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSmono : ∀ ω, Monotone (fun k => S k ω))
    (hSsup : ∀ ω, (⨆ k : ℕ, S k ω) = ⊤)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (τk : ℕ → Ω → ℝ≥0)
    (hτk : ∀ k ω, τk k ω =
      (min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal)
    (W Cash Term : Ω → ℝ)
    (Wk Cashk Termk : ℕ → Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)
    (w : ℝ → ℝ)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hWk : ∀ k ω, Wk k ω =
      if τk k ω = 0 ∨ (τk k ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τk k ω) ω - rightLimit D (τk k ω) ω
      else riskProcess X x D (τk k ω) ω)
    (hCashk : ∀ k ω, Cashk k ω =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τk k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)
    (hTermk : ∀ k ω, Termk k ω =
      Real.exp (-(q * (τk k ω : ℝ))) * w (Wk k ω)) :
    ∀ ω, ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      τk k ω = τ ω ∧ Wk k ω = W ω ∧
      Cashk k ω = Cash ω ∧ Termk k ω = Term ω := by
  intro ω
  have hlt : (n : ℝ≥0∞) < (⨆ k : ℕ, S k ω) := by
    rw [hSsup ω]
    simp
  obtain ⟨K, hK⟩ := lt_iSup_iff.mp hlt
  refine ⟨K, ?_⟩
  intro k hk
  have hτle : min (ruinTime X x D ω) (n : ℝ≥0∞) ≤ S k ω :=
    (min_le_right _ _).trans ((le_of_lt hK).trans (hSmono ω hk))
  have hClock : τk k ω = τ ω := by
    rw [hτk k ω, min_eq_left hτle]
    exact (hτ ω).symm
  have hReserve : Wk k ω = W ω := by
    rw [hWk k ω, hW ω, hClock]
  have hCashEq : Cashk k ω = Cash ω := by
    rw [hCashk k ω, hCash ω, hClock]
  have hTermEq : Termk k ω = Term ω := by
    rw [hTermk k ω, hTerm ω, hClock, hReserve]
  exact ⟨hClock, hReserve, hCashEq, hTermEq⟩
