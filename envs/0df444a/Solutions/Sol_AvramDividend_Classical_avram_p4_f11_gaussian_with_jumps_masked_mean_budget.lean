-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f11_gaussian_with_jumps_masked_mean_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:00:12.8296+00:00
-- url     : https://prove2.me/submissions/610c02b5-fc3a-4ca9-bfb2-4981e223d113
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_mixed_gaussian_negativejump_signed_budget
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_rightcont_stopping_zero_mask_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuNonzero : X.ν ≠ 0) (q : ℝ) (hq : 0 < q)
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
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P) :
    ∀ k, (∫ ω, (if σ k ω = 0 then w x else F k ω) ∂P) ≤ w x := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro k
  obtain ⟨Mc, Ms, Ml, G, R, hMcI, hMsI, hMlI,
      hMcMean, hMsMean, hMlMean, hG, hR, hUpper⟩ :=
    avram_ubv_loc6_mixed_gaussian_negativejump_signed_budget
      X hX hBV hNuNonzero hSigmaNonzero q hq w C hC
      hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop
      W Cash Term hW hCash hTerm hTermMeas hCashI
      σ F hσstop hσle hFsource hFI k
  have hMaskI :
      Integrable (fun ω => if σ k ω = 0 then w x else F k ω) P :=
    avram_ubv_loc6_rightcont_stopping_zero_mask_integrable
      (σ k) (hσstop k) (F k) (hFI k) (w x)
  let M : Ω → ℝ := fun ω => Mc ω + (Ms ω + Ml ω)
  have hMI : Integrable M P := hMcI.add (hMsI.add hMlI)
  have hMZero : (∫ ω, M ω ∂P) = 0 := by
    change (∫ ω, (Mc + (Ms + Ml)) ω ∂P) = 0
    calc
      _ = (∫ ω, Mc ω ∂P) + (∫ ω, (Ms + Ml) ω ∂P) :=
        integral_add hMcI (hMsI.add hMlI)
      _ = (∫ ω, Mc ω ∂P) +
          ((∫ ω, Ms ω ∂P) + (∫ ω, Ml ω ∂P)) := by
        congr 1
        exact integral_add hMsI hMlI
      _ = 0 := by simp [hMcMean, hMsMean, hMlMean]
  have hRightI : Integrable (fun ω => w x + M ω) P :=
    (integrable_const (w x)).add hMI
  have hPoint :
      ∀ᵐ ω ∂P, (if σ k ω = 0 then w x else F k ω) ≤ w x + M ω := by
    filter_upwards [hG, hR, hUpper] with ω hg hr hu
    dsimp [M]
    linarith only [hu, hg, hr]
  calc
    (∫ ω, (if σ k ω = 0 then w x else F k ω) ∂P)
        ≤ ∫ ω, (w x + M ω) ∂P :=
      integral_mono_ae hMaskI hRightI hPoint
    _ = (∫ ω, w x ∂P) + (∫ ω, M ω ∂P) :=
      integral_add (integrable_const (w x)) hMI
    _ = w x := by simp [hMZero]
