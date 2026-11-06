-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit1_ubv_uniform_positive_source_to_dividendValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T01:28:27.076197+00:00
-- url     : https://prove2.me/submissions/6cb9a8a9-0e45-4354-b3ec-2cb0141d87e0

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit1_ubv_original_single_residual_to_stopped_cash
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Positive integer original UBV residual witnesses yield perpetual Stieltjes
    value, preserving the initial atom via n+1 and retaining right endpoints. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hEvidence : ∀ k : ℕ, 0 < k →
      ∃ (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ),
        (∀ ω, τ ω =
          (min (ruinTime X x D ω) (k : ℝ≥0∞)).toNNReal) ∧
        Measurable (fun ω => (τ ω : ℝ)) ∧
        (∀ ω, W ω = if τ ω = 0 ∨
          (τ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
          else riskProcess X x D (τ ω) ω) ∧
        (∀ ω, Cash ω = (∫⁻ s in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal) ∧
        (∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) ∧
        Integrable Cash P ∧
        (∃ M G H : Ω → ℝ,
          Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
          (∫ ω, M ω ∂P) = 0 ∧
          (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
          (∀ᵐ ω ∂P, Term ω + Cash ω ≤
            w x + M ω + G ω + H ω))) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
  apply avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue
    X q x D hD.1 (ENNReal.ofReal (w x))
  intro n
  obtain ⟨τ, W, Cash, Term, hτeq, hτMeas, hW, hCash, hTerm,
    hCashI, hSource⟩ := hEvidence (n + 1) (Nat.succ_pos n)
  have hStopped := avram_limit1_ubv_original_single_residual_to_stopped_cash
    X hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
    x hxc D hD (n + 1) τ hτeq hτMeas W Cash Term
    hW hCash hTerm hCashI hSource
  calc
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P)
        ≤ (∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) := by
              apply lintegral_mono
              intro ω
              apply lintegral_mono_set
              intro t ht
              have hIndex : (n : ℝ≥0∞) ≤ ((n + 1 : ℕ) : ℝ≥0∞) := by
                exact_mod_cast Nat.le_succ n
              have ht' : t ∈ paymentTimes
                  (min (ruinTime X x D ω) ((n + 1 : ℕ) : ℝ≥0∞)) :=
                paymentTimes_min_mono_horizon
                  (ruinTime X x D ω) (n : ℝ≥0∞)
                  ((n + 1 : ℕ) : ℝ≥0∞) hIndex ht
              have hpay : t ∈ paymentTimes (ruinTime X x D ω) := by
                refine ⟨ht'.1, ?_⟩
                rcases ht'.2 with hzero | hlt
                · exact Or.inl hzero
                · exact Or.inr (lt_of_lt_of_le hlt (min_le_left _ _))
              have hτle : t ≤ (τ ω : ℝ) := by
                rcases ht'.2 with hzero | hlt
                · rw [hzero]
                  positivity
                · have hfinite :
                    min (ruinTime X x D ω)
                        ((n + 1 : ℕ) : ℝ≥0∞) < ⊤ :=
                    lt_of_le_of_lt (min_le_right _ _) ENNReal.coe_lt_top
                  have hcast :
                      (τ ω : ℝ≥0∞) =
                        min (ruinTime X x D ω)
                          ((n + 1 : ℕ) : ℝ≥0∞) := by
                    rw [hτeq ω]
                    exact ENNReal.coe_toNNReal (ne_of_lt hfinite)
                  have hlt' : ENNReal.ofReal t < (τ ω : ℝ≥0∞) := by
                    rw [hcast]
                    exact hlt
                  exact le_of_lt ((ENNReal.ofReal_lt_coe_iff ht'.1).mp hlt')
              exact ⟨hpay, hτle⟩
    _ ≤ ENNReal.ofReal (w x) := hStopped
