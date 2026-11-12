-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB61_original_finitecap_postpayment_coeff_refinement_energy
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:45:19.488997+00:00
-- url     : https://prove2.me/submissions/cc0a67c5-d44a-4ac8-98a9-5d45bb498a63
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB65_original_finitecap_stopped_gradient_time_L2_energy_cauchy
import Theorems.Thm_AvramDividend_Classical_avram_gbB82_original_two_mesh_time_energy_grid_exact
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
      Tendsto E atTop (𝓝 (0 : ℝ)) := by
  intro k ρ hρstop hρle δ hδ hFloor A hA j G E
  let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    (Finset.range (m + 1)).sum (fun i =>
      if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ)
      then G m i ω else 0)
  have hTime : Tendsto (fun nm : ℕ × ℕ => (∫ t in Ioo (0 : ℝ) (n : ℝ),
          (∫ ω, (K nm.1 t ω - K nm.2 t ω) ^ 2 ∂P) ∂volume))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [K, G] using
      (avram_gbB65_original_finitecap_stopped_gradient_time_L2_energy_cauchy
        X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg hw_smooth hw_gen
        hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop σ hσstop
        hσle k ρ hρstop hρle δ hδ hFloor A hA j)
  have hGrid : ∀ (m p : ℕ), E (m, p) =
      (∫ t in Ioo (0 : ℝ) (n : ℝ),
        (∫ ω, (K m t ω - K p t ω) ^ 2 ∂P) ∂volume) := by
    simpa only [K, G, E] using
      (avram_gbB82_original_two_mesh_time_energy_grid_exact
        X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg hw_smooth hw_gen
        hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop σ hσstop
        hσle k ρ hρstop hρle δ hδ hFloor A hA j)
  have hEq : E = fun nm : ℕ × ℕ => (∫ t in Ioo (0 : ℝ) (n : ℝ),
          (∫ ω, (K nm.1 t ω - K nm.2 t ω) ^ 2 ∂P) ∂volume) := by
    funext nm
    rcases nm with ⟨m, p⟩
    exact hGrid m p
  rw [hEq]
  exact hTime
