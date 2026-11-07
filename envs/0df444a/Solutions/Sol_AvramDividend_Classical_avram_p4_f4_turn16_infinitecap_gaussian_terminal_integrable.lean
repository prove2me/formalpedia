-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_turn16_infinitecap_gaussian_terminal_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:27:35.237329+00:00
-- url     : https://prove2.me/submissions/dc2fcc9b-0796-42b7-b41f-d29f1aa4aae2

import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn16_gaussian_HJB_global_exponential_growth
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_le_finite_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_infinite_cap_discounted_terminal_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_terminal_L1_of_bounded_exp_growth_any_q
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal


noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hCtop : C = ⊤) :
    Integrable Term P := by
  obtain ⟨θ, K, hθ, hK, hGrowth⟩ :=
    AvramDividend.Classical.avram_p4_f4_turn16_gaussian_HJB_global_exponential_growth
      X hX hBV hν q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad hCtop
  have hBound : ∀ ω, τ ω ≤ (n : ℝ≥0) :=
    AvramDividend.Classical.avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_le_finite_horizon
      X x D n τ hτeq
  have hNonneg : ∀ᵐ ω ∂P, 0 ≤ Term ω := Filter.Eventually.of_forall <|
    AvramDividend.Classical.avram_p4_f_assembly_original_infinite_cap_discounted_terminal_nonnegative
      X q w C hCtop hw0 hw_cont hw_neg hw_smooth hw_grad x D τ W Term hW hTerm
  exact AvramDividend.Classical.avram_p4_f_assembly_original_terminal_L1_of_bounded_exp_growth_any_q
    X C x D hD τ W Term hτmeas hτstop (n : ℝ≥0) hBound hW
    w q θ K hθ hK hGrowth hTerm hTermMeas hNonneg
