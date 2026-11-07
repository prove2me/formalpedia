-- Prove2me | solution 6 for AvramDividend.Classical.avram_wave7_08_source_original_ito_martingale_residual_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:03:33.510093+00:00
-- url     : https://prove2.me/submissions/9c27e1f1-2e9b-418d-93ed-b2b5db4b33ed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_integration_p4_original_stopped_source_components_public
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
    ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω) := by
  obtain ⟨Mc, Ms, Ml, G, R, hMcI, hMsI, hMlI, hGI,
      hMc0, hMs0, hMl0, hGle, hRle, hbudget⟩ :=
    avram_integration_p4_original_stopped_source_components_public
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop
      W Cash Term hW hCash hTerm hTermMeas hCashI
  refine ⟨fun ω => Mc ω + Ms ω + Ml ω, G, fun _ => 0,
    (hMcI.add hMsI).add hMlI, hGI, integrable_zero _ _ _, ?_, ?_, ?_⟩
  · have hPair :
        (∫ ω, Mc ω + Ms ω ∂P) =
          (∫ ω, Mc ω ∂P) + (∫ ω, Ms ω ∂P) := by
      simpa only [Pi.add_apply] using (integral_add hMcI hMsI)
    have hTrio :
        (∫ ω, Mc ω + Ms ω + Ml ω ∂P) =
          (∫ ω, Mc ω + Ms ω ∂P) + (∫ ω, Ml ω ∂P) := by
      simpa only [Pi.add_apply] using
        (integral_add (hMcI.add hMsI) hMlI)
    calc
      (∫ ω, Mc ω + Ms ω + Ml ω ∂P) =
          (∫ ω, Mc ω + Ms ω ∂P) +
            (∫ ω, Ml ω ∂P) := hTrio
      _ = 0 := by rw [hPair, hMc0, hMs0, hMl0]; norm_num
  · filter_upwards [hGle] with ω hG
    simpa using hG
  · filter_upwards [hbudget, hRle] with ω hB hR
    have hdrop :
        w x + Mc ω + Ms ω + Ml ω + G ω + R ω ≤
          w x + (Mc ω + Ms ω + Ml ω) + G ω + 0 := by
      linarith
    exact hB.trans hdrop
