-- Prove2me | solution 2 for AvramDividend.Classical.avram_p4_f4_mixed_gaussian_jump_top_cap_ennreal_expected_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:59:38.713214+00:00
-- url     : https://prove2.me/submissions/b3744e48-42c2-485a-9bb9-24619cb538fa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_stopped_terminal_integrable_natural_clock
import Theorems.Thm_AvramDividend_Classical_avram_p4_f5_topcap_components_given_terminal_l1
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_five_witness_iff_expected_budget
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_topcap_original_stopped_closed_payoff_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_limit2_integrable_nonnegative_real_grid_to_ennreal_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
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
    (hCashI : Integrable Cash P) (hTop : C = ⊤) :
    (∫⁻ ω, ENNReal.ofReal (Term ω + Cash ω) ∂P) ≤ ENNReal.ofReal (w x) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hTI : Integrable Term P :=
    avram_p4_f4_original_stopped_terminal_integrable_natural_clock
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm hTermMeas hCashI
  obtain ⟨Mc, Ms, Ml, G, R, hMcI, hMsI, hMlI, hGI, hRI,
      hMc0, hMs0, hMl0, hVanish, hG, hR, hIto⟩ :=
    avram_p4_f5_topcap_components_given_terminal_l1
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
      hTermMeas hCashI hTI hTop
  have hMean : (∫ ω, Term ω + Cash ω ∂P) ≤ w x := by
    apply (avram_p4_f4_five_witness_iff_expected_budget
      Term Cash hTI hCashI (w x)).2
    exact ⟨Mc, Ms, Ml, G, R, hMcI, hMsI, hMlI, hGI,
      hMc0, hMs0, hMl0, hG, hR, hIto⟩
  have hNonneg : ∀ ω, 0 ≤ Term ω + Cash ω :=
    avram_ubv_loc6_topcap_original_stopped_closed_payoff_nonnegative
      X x q D τ w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      W Cash Term hW hCash hTerm hTop
  have hBound :=
    avram_limit2_integrable_nonnegative_real_grid_to_ennreal_budget
      (F := fun _ : ℕ => fun ω => Term ω + Cash ω) (B := w x)
      (hInt := by intro k; exact hTI.add hCashI)
      (hNonneg := by intro k; exact Filter.Eventually.of_forall hNonneg)
      (hMean := by intro k; exact hMean)
  exact hBound 0
