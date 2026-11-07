-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_purejump_finitecap_physical_HJB_mean
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:52:40.130844+00:00
-- url     : https://prove2.me/submissions/63b28010-dd91-497e-9bca-4b94bf87e973
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f5_original_stopped_fatou_localisation_certificate
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_natural_clock_three_signs
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_ae_local_fatou_to_original_five_witness
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_five_source_witnesses_drop_nonintegrable_R_signed
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_finitecap_reward_L1_nonnegative
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

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
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ = 0) (q : ℝ) (hq : 0 < q)
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
    (hFinite : C ≠ ⊤) :
    (∫ ω, Term ω + Cash ω ∂P) ≤ w x := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hRI : Integrable (fun ω => Term ω + Cash ω) P :=
    (avram_p4_f4_original_finitecap_reward_L1_nonnegative
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen
      hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas
      hτstop W Cash Term hW hCash hTerm hTermMeas hCashI hFinite).1
  obtain ⟨σ, F, hwx, hStop, hBound, hExact, hMeas, hInt, hNN, hLim, hBudget⟩ :=
    avram_p4_f5_original_stopped_fatou_localisation_certificate
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen
      hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas
      hτstop W Cash Term hW hCash hTerm hTermMeas hCashI
  obtain ⟨_, hTermNN, hCashNN⟩ :=
    avram_p4_f4_original_natural_clock_three_signs
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen
      hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas
      hτstop W Cash Term hW hCash hTerm hTermMeas hCashI
  have hSource :=
    avram_p4_f4_ae_local_fatou_to_original_five_witness
      Term Cash hTermMeas hCashI hTermNN hCashNN
      F hMeas hInt hNN hLim (w x) hwx hBudget
  obtain ⟨M, G, H, hMI, hGI, hHI, hMzero, hGHsign, hFM⟩ :=
    avram_p4_f3_five_source_witnesses_drop_nonintegrable_R_signed
      Term Cash (w x) hSource
  have hGHInt : Integrable (fun ω => G ω + H ω) P := hGI.add hHI
  have hGMInt : Integrable (fun ω => w x + M ω) P :=
    (integrable_const (w x)).add hMI
  have hTotalInt :
      Integrable (fun ω => (w x + M ω) + (G ω + H ω)) P :=
    hGMInt.add hGHInt
  have hFM' : ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤ (w x + M ω) + (G ω + H ω) := by
    filter_upwards [hFM] with ω hω
    simpa only [add_assoc] using hω
  have hFirst := integral_mono_ae hRI hTotalInt hFM'
  have hFirst' :
      (∫ ω, Term ω + Cash ω ∂P) ≤
          (∫ ω, w x + M ω ∂P) + (∫ ω, G ω + H ω ∂P) := by
    simpa only [integral_add hGMInt hGHInt] using hFirst
  have hMeanGM : (∫ ω, w x + M ω ∂P) = w x := by
    rw [integral_add (integrable_const (w x)) hMI]
    simp only [hMzero, add_zero]
    simp
  have hGHnonpos : (∫ ω, G ω + H ω ∂P) ≤ 0 := by
    have hcmp := integral_mono_ae hGHInt (integrable_const (0 : ℝ)) hGHsign
    simpa using hcmp
  rw [hMeanGM] at hFirst'
  linarith
