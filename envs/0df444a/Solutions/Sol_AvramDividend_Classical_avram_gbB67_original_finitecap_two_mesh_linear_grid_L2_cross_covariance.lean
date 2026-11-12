-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB67_original_finitecap_two_mesh_linear_grid_L2_cross_covariance
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:57:08.647987+00:00
-- url     : https://prove2.me/submissions/9274538a-00cb-4f55-8d14-d449fee7ec18
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB76_original_two_uniform_grid_generic_predictable_covariance
import Theorems.Thm_AvramDividend_Classical_avram_gbB53_original_finitecap_postpayment_gradient_grid_regular
import Theorems.Thm_AvramDividend_Classical_avram_gbB59_original_finitecap_postpayment_gradient_grid_filtered
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
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧
      X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0) (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
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
      let L : ℕ → Ω → ℝ := fun m ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → Ω → ℝ := fun i η => x + X.X (s i) η - rightLimit D (s i) η
        let Z : ℕ → Ω → ℝ := fun i η => X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
        let G : ℕ → Ω → ℝ := fun i η => if s i < ρ η then Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ∈ Icc a b then deriv w (Y i η) else 1)
          else 0
        let H : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then (1 / 2 : ℝ) *
            Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ∈ Icc a b then iteratedDeriv 2 w (Y i η) else 0)
          else 0
        (Finset.range (m + 1)).sum (fun i => G i ω * Z i ω)
      let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → Ω → ℝ := fun i η => x + X.X (s i) η - rightLimit D (s i) η
        let G : ℕ → Ω → ℝ := fun i η => if s i < ρ η then Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ∈ Icc a b then deriv w (Y i η) else 1)
          else 0
        (Finset.range (m + 1)).sum (fun i =>
          if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ)
          then G i ω else 0)
      ∀ m l,
        (∫ ω, (L m ω) * (L l ω) ∂P) =
          X.σ ^ 2 *
            (∫ t in Ioo (0 : ℝ) (n : ℝ),
              (∫ ω, (K m t ω) * (K l t ω) ∂P) ∂volume) := by
  intro k ρ hρstop hρle δ hδ hFloor A hA j L K m l
  let G : ℕ → ℕ → Ω → ℝ := fun h i ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((h + 1 : ℕ) : ℝ≥0)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let a : ℝ := δ / 2
    let b : ℝ := C.toReal *
      (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let Y : ℝ := x + X.X s ω - rightLimit D s ω
    if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
      (if Y ∈ Icc a b then deriv w Y else 1)
    else 0
  have ha : ∀ (h i : ℕ), Measurable[𝓕.rightCont
      ((i : ℝ≥0) * ((n : ℝ≥0) / ((h + 1 : ℕ) : ℝ≥0)))]
      (G h i) := by
    intro h i
    simpa only [G] using
      (avram_gbB59_original_finitecap_postpayment_gradient_grid_filtered
        X q hq w C hC hFiniteCap hw_smooth x D hD n hn ρ hρstop
        δ hδ j h i)
  obtain ⟨B, hB0, hB53⟩ :=
    avram_gbB53_original_finitecap_postpayment_gradient_grid_regular
      X q hq w C hC hFiniteCap hw_smooth x D hD n hn ρ hρstop δ hδ j
  have hb : ∃ B : ℝ, 0 ≤ B ∧ ∀ (h i : ℕ) (ω : Ω), |G h i ω| ≤ B := by
    refine ⟨B, hB0, ?_⟩
    intro h i ω
    simpa only [G] using (hB53 h i).2 ω
  have h :=
    avram_gbB76_original_two_uniform_grid_generic_predictable_covariance
      X hν n hn G ha hb m l
  simpa only [L, K, G] using h
