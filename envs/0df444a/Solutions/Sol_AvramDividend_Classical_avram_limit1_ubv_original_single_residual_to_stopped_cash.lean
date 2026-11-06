-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit1_ubv_original_single_residual_to_stopped_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T01:00:10.294195+00:00
-- url     : https://prove2.me/submissions/ab12fb8a-bd65-474f-ad4f-955a6d7f8be3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_le_finite_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
import Theorems.Thm_AvramDividend_Classical_avram_limit1_bounded_clock_stopped_residual_to_ennreal_cash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Source-exact P4-F one-martingale stopped residual implies original
    ENNReal cash, with terminal positivity and clock bound discharged. -/
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
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hCashI : Integrable Cash P)
    (hSource : ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        w x + M ω + G ω + H ω)) :
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by
  obtain ⟨M, G, H, hMI, hGI, hHI, hMZero, hGH, hResidual⟩ := hSource
  have hτBound : ∀ ω, τ ω ≤ (n : ℝ≥0) :=
    avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_le_finite_horizon
      X x D n τ hτeq
  have hTermPoint : ∀ ω, 0 ≤ Term ω :=
    avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD q τ W Term hW hTerm
  exact avram_limit1_bounded_clock_stopped_residual_to_ennreal_cash
    X x C D hD q (le_of_lt hq) (n : ℝ≥0) τ hτBound hτMeas
    (w x) Cash Term M G H hCash hCashI hMI hMZero
    (Filter.Eventually.of_forall hTermPoint) hGH hResidual
