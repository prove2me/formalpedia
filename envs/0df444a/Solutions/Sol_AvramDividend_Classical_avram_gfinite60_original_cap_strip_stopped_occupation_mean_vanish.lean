-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite60_original_cap_strip_stopped_occupation_mean_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T23:43:44.938625+00:00
-- url     : https://prove2.me/submissions/029e4a29-2e25-4683-b504-e35a4cd7c7aa

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gfinite62_original_cap_strip_occupation_measurable_ae_vanish
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
      let b : ℕ → ℝ := fun j =>
        C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let Occ : ℕ → Ω → ℝ := fun j ω =>
        ∫ t in Ioo (0 : ℝ) (n : ℝ),
          if t < (ρ ω : ℝ) ∧
              b j < riskProcess X x D (Real.toNNReal t) ω
          then (1 : ℝ) else 0 ∂volume
      Tendsto (fun j : ℕ => ∫ ω in A, Occ j ω ∂P)
        atTop (𝓝 (0 : ℝ)) := by
  classical
  intro k ρ hρstop hρle δ hδ hFloor A hA
  let b : ℕ → ℝ := fun j =>
    C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  let Occ : ℕ → Ω → ℝ := fun j ω =>
    ∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (ρ ω : ℝ) ∧
          b j < riskProcess X x D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume
  obtain ⟨hMeas, hBound, hConv⟩ :=
    avram_gfinite62_original_cap_strip_occupation_measurable_ae_vanish
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
      τ hτeq hτmeas hτstop σ hσstop hσle k ρ hρstop hρle
      δ hδ hFloor A hA
  letI : IsProbabilityMeasure P := X.isProbability
  have hDom : ∀ j : ℕ, ∀ᵐ ω ∂P,
      ‖A.indicator (Occ j) ω‖ ≤ (n : ℝ) := by
    intro j
    exact Filter.Eventually.of_forall (hBound j)
  have hDCT :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : Ω => (n : ℝ)) hMeas
      (integrable_const (n : ℝ)) hDom hConv
  have hAmeas : MeasurableSet A :=
    (𝓕.rightCont.le 0) A hA
  simpa [Occ, b, integral_indicator hAmeas] using hDCT
