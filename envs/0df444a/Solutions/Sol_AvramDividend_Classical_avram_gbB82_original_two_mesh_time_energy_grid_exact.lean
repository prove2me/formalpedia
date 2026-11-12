-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB82_original_two_mesh_time_energy_grid_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:14:44.284056+00:00
-- url     : https://prove2.me/submissions/7fff8427-4195-49b7-a7c9-602699dcdec0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB53_original_finitecap_postpayment_gradient_grid_regular
import Theorems.Thm_AvramDividend_Classical_avram_gbB97_bounded_step_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_gbB98_two_mesh_step_energy_integral_transfer
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 < q)
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
      let G : ℕ → ℕ → Ω → ℝ := fun m i ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal *
          (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℝ := x + X.X s ω - rightLimit D s ω
        if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
          (if Y ∈ Icc a b then deriv w Y else 1)
        else 0
      let E : ℕ × ℕ → ℝ := fun nm =>
        let m : ℕ := nm.1
        let p : ℕ := nm.2
        let N : ℕ := (m + 1) * (p + 1)
        let Δ : ℝ := (n : ℝ) / (N : ℝ)
        Δ * (Finset.range N).sum (fun i =>
          ∫ ω, (G m (i / (p + 1)) ω -
            G p (i / (m + 1)) ω) ^ 2 ∂P)
      let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        (Finset.range (m + 1)).sum (fun i =>
          if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ)
          then G m i ω else 0)
      ∀ (m p : ℕ), E (m, p) =
        (∫ t in Ioo (0 : ℝ) (n : ℝ),
          (∫ ω, (K m t ω - K p t ω) ^ 2 ∂P) ∂volume) := by
  intro k ρ hρstop hρle δ hδ hFloor A hA j G E K m p
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨B, hB, hG⟩ :=
    avram_gbB53_original_finitecap_postpayment_gradient_grid_regular
      X q hq w C hC hFiniteCap hw_smooth x D hD
      n hn ρ hρstop δ hδ j
  have hF : ∀ r, Integrable (fun ω =>
      (G m (r / (p + 1)) ω -
        G p (r / (m + 1)) ω) ^ 2) P := by
    intro r
    exact avram_gbB97_bounded_step_square_integrable P G
      (fun a i => (hG a i).1) B hB
      (fun a i ω => (hG a i).2 ω) m p r
  exact (avram_gbB98_two_mesh_step_energy_integral_transfer
    P n m p hn G hF).symm
