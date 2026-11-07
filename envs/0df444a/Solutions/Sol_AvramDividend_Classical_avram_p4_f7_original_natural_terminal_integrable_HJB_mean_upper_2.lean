-- Prove2me | solution 2 for AvramDividend.Classical.avram_p4_f7_original_natural_terminal_integrable_HJB_mean_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:35:09.326897+00:00
-- url     : https://prove2.me/submissions/b9e2a23d-52a2-4ef8-8600-9d3406643989
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_natural_clock_three_signs
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_compact_clock_exact_payoff_convergence
import Theorems.Thm_AvramDividend_Classical_avram_p4_f7_original_any_integrable_exact_clock_expected_upper
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_ae_natural_clock_fatou_L1_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
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
    (hCashI : Integrable Cash P) :
    Integrable Term P ∧
      (∫ ω, Term ω + Cash ω ∂P) ≤ w x := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨hb, hTermPos, hCashPos⟩ :=
    avram_p4_f4_original_natural_clock_three_signs
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop W Cash Term
      hW hCash hTerm hTermMeas hCashI
  obtain ⟨σ, F, _, hσstop, hσle, hFsource, hFmeas, hFI, hFpos, hlim⟩ :=
    avram_f6_original_compact_clock_exact_payoff_convergence
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop W Cash Term
      hW hCash hTerm hTermMeas hCashI
  have hBudget : ∀ k, (∫ ω, F k ω ∂P) ≤ w x :=
    avram_p4_f7_original_any_integrable_exact_clock_expected_upper
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop W Cash Term
      hW hCash hTerm hTermMeas hCashI
      σ F hσstop hσle hFsource hFI
  have hSmeas :
      AEStronglyMeasurable (fun ω => Term ω + Cash ω) P :=
    hTermMeas.add hCashI.aestronglyMeasurable
  have hSpos : 0 ≤ᵐ[P] (fun ω => Term ω + Cash ω) := by
    filter_upwards [hTermPos, hCashPos] with ω ht hc
    exact add_nonneg ht hc
  obtain ⟨hSI, hMean⟩ :=
    avram_p4_f4_ae_natural_clock_fatou_L1_budget
      P (fun ω => Term ω + Cash ω) F hSmeas hSpos
      hFmeas hFI hFpos hlim (w x) hb hBudget
  have hTermI : Integrable Term P := by
    have heq : ((fun ω => Term ω + Cash ω) - Cash) = Term := by
      funext ω
      change (Term ω + Cash ω) - Cash ω = Term ω
      ring
    simpa only [heq] using hSI.sub hCashI
  exact ⟨hTermI, hMean⟩
