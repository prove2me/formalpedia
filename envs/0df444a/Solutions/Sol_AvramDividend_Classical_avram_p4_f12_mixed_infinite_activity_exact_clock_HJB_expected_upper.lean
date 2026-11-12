-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f12_mixed_infinite_activity_exact_clock_HJB_expected_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:46:09.307335+00:00
-- url     : https://prove2.me/submissions/0215434b-5f8a-4c99-81b2-65a2d9628805
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_infinite_activity_positive_clock
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_positive_clock_mask_residual_identity
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_original_zero_clock_mask_dominates_unmasked_mean
import Theorems.Thm_AvramDividend_Classical_avram_f16_original_masked_sigma_payoff_integrable


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
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
    (hFI : ∀ k, Integrable (F k) P)
    (hν : X.ν ≠ 0)
    (hσnz : X.σ ≠ 0)
    (hInfiniteActivity : X.ν (Iio (0 : ℝ)) = ⊤) :
    ∀ k, (∫ ω, F k ω ∂P) ≤ w x := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k
  let A : Set Ω := {ω | σ k ω = 0}
  have hA : MeasurableSet A := avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
      𝓕 (σ k) (hσstop k)
  have hPositive : (∫ ω in Aᶜ, F k ω ∂P) ≤
      w x * (P Aᶜ).toReal := by
    change (∫ ω in {ω : Ω | σ k ω ≠ 0}, F k ω ∂P) ≤
      w x * (P {ω : Ω | σ k ω ≠ 0}).toReal
    exact avram_ubv_mixed12_infinite_activity_positive_clock
        X hX hBV hν hσnz q hq w C hC hw0 hw_cont hw_neg
        hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
        n hn τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
        hTermMeas hCashI σ F hσstop hσle hFsource hFI
        hInfiniteActivity k
  have hPositiveResidual : (∫ ω in Aᶜ, F k ω - w x ∂P) ≤ 0 := by
    rw [integral_sub (hFI k).integrableOn
      (integrable_const (w x)).integrableOn, setIntegral_const]
    change (∫ ω in Aᶜ, F k ω ∂P) - (P Aᶜ).toReal * w x ≤ 0; nlinarith [hPositive]
  have hMaskedResidual :
      (∫ ω, (if σ k ω = 0 then w x else F k ω) - w x ∂P) ≤ 0 := by
    change (∫ ω, (if ω ∈ A then w x else F k ω) - w x ∂P) ≤ 0
    rw [avram_p4_f12_positive_clock_mask_residual_identity
      P A hA (F k) (hFI k) (w x)]
    exact hPositiveResidual
  have hMaskI : Integrable
      (fun ω => if σ k ω = 0 then w x else F k ω) P :=
    avram_f16_original_masked_sigma_payoff_integrable
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
      hTermMeas hCashI σ F hσstop hσle hFsource hFI k
  have hMaskMean :
      (∫ ω, (if σ k ω = 0 then w x else F k ω) ∂P) ≤ w x := by
    have hSub := hMaskedResidual
    have hc : (∫ _ : Ω, (w x : ℝ) ∂P) = w x := by simp
    rw [integral_sub hMaskI (integrable_const (w x)), hc] at hSub
    linarith
  have hUnmasked :
      (∫ ω, F k ω ∂P) ≤
      ∫ ω, (if σ k ω = 0 then w x else F k ω) ∂P :=
    avram_p4_f12_original_zero_clock_mask_dominates_unmasked_mean
      X x q w C D hD hjump σ F hFsource hFI
      (fun j => avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
        𝓕 (σ j) (hσstop j)) k
  exact le_trans hUnmasked hMaskMean
