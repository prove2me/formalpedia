-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB54w_original_finitecap_discounted_cash_corner_strip_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:56:00.884893+00:00
-- url     : https://prove2.me/submissions/a3a5fee5-d77d-434e-bdec-15d8b24fc24d

import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Theorems.Thm_AvramDividend_Classical_avram_gfinite28_original_bounded_stop_masked_strict_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_gb26_original_finitecap_strip_event_integrable
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
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
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k (ρ : Ω → ℝ≥0)
      (hρstop : IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ ω : WithTop ℝ≥0)))
      (hρle : ∀ ω, ρ ω ≤ σ k ω)
      (δ : ℝ) (hδ : 0 < δ)
      (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
        δ ≤ riskProcess X x D t ω)
      (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
    ∀ (j : ℕ),
      let b : ℝ := C.toReal *
          (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let F : Ω → ℝ := fun ω =>
          if ρ ω = 0 then w x else
            Real.exp (-(q * (ρ ω : ℝ))) *
              w (riskProcess X x D (ρ ω) ω) +
            (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
              ENNReal.ofReal (Real.exp (-(q * z)))
              ∂(dividendMeasure D ω)).toReal
      let Occ : Ω → ℝ := fun ω =>
          ∫ t in Ioo (0 : ℝ) (n : ℝ),
            if t < (ρ ω : ℝ) ∧
                b < riskProcess X x D (Real.toNNReal t) ω
            then (1 : ℝ) else 0 ∂volume
      Integrable
        (fun ω => (F ω - w x) -
          (((w C.toReal - w b) - (C.toReal - b)) +
            max X.c 0 * Occ ω))
        (P.restrict A) := by
  classical
  intro k ρ hρstop hρle δ hδ hFloor A hA j b F Occ
  letI : IsProbabilityMeasure P := X.isProbability
  have hτ : ∀ ω, τ ω ≤ (n : ℝ≥0) := by
    intro ω
    rw [hτeq ω]
    exact (avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n).2.1 ω
  have hρbound (ω : Ω) : ρ ω ≤ (n : ℝ≥0) :=
    (hρle ω).trans ((hσle k ω).trans (hτ ω))
  have hFI : Integrable F (P.restrict A) := by
    have hF := avram_gfinite28_original_bounded_stop_masked_strict_reward_L1
      X x C hFiniteCap hxc D hD w hw_cont hw_neg q hq ρ hρstop n hρbound
    simpa only [F] using hF.mono_measure Measure.restrict_le_self
  have hOccI : Integrable Occ (P.restrict A) := by
    have hOcc := (avram_gb26_original_finitecap_strip_event_integrable
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg hw_smooth hw_gen
      hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop
      σ hσstop hσle k ρ hρstop hρle δ hδ hFloor A hA j).1
    simpa only [Occ] using hOcc.integrable
  haveI : IsFiniteMeasure (P.restrict A) := inferInstance
  have hWX : Integrable (fun _ : Ω => w x) (P.restrict A) :=
    integrable_const (w x)
  have hCorner : Integrable
      (fun _ : Ω => (w C.toReal - w b) - (C.toReal - b))
      (P.restrict A) := integrable_const _
  exact (hFI.sub hWX).sub
    (hCorner.add (hOccI.const_mul (max X.c 0)))
