-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb94_original_finitecap_grid_coefficients_time_L2_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:14:30.444535+00:00
-- url     : https://prove2.me/submissions/9150bb5f-8281-409d-b4c6-7e67eb309a0f

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_avram_gbB53_original_finitecap_postpayment_gradient_grid_regular
import Theorems.Thm_AvramDividend_Classical_avram_gb95_finite_step_pair_L2_time_integrable
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
      let L : ℕ → Ω → ℝ := fun m ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → Ω → ℝ := fun i η => x + X.X (s i) η - rightLimit D (s i) η
        let Z : ℕ → Ω → ℝ := fun i η => X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
        let G : ℕ → Ω → ℝ := fun i η => if s i < ρ η then Real.exp (-(q * (s i : ℝ))) * (if Y i η ∈ Icc a b then deriv w (Y i η) else 1) else 0
        let H : ℕ → Ω → ℝ := fun i η => if s i < ρ η then (1 / 2 : ℝ) * Real.exp (-(q * (s i : ℝ))) * (if Y i η ∈ Icc a b then iteratedDeriv 2 w (Y i η) else 0) else 0
        (Finset.range (m + 1)).sum (fun i => G i ω * Z i ω)
      let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → Ω → ℝ := fun i η => x + X.X (s i) η - rightLimit D (s i) η
        let G : ℕ → Ω → ℝ := fun i η => if s i < ρ η then Real.exp (-(q * (s i : ℝ))) * (if Y i η ∈ Icc a b then deriv w (Y i η) else 1) else 0
        (Finset.range (m + 1)).sum (fun i => if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ) then G i ω else 0)
      ∀ m l,
        (∀ t : ℝ,
          Integrable (fun ω => (K m t ω) ^ 2) P ∧
          Integrable (fun ω => (K l t ω) ^ 2) P ∧
          Integrable (fun ω => K m t ω * K l t ω) P) ∧
        IntegrableOn (fun t => ∫ ω, (K m t ω) ^ 2 ∂P)
          (Ioo (0 : ℝ) (n : ℝ)) volume ∧
        IntegrableOn (fun t => ∫ ω, (K l t ω) ^ 2 ∂P)
          (Ioo (0 : ℝ) (n : ℝ)) volume ∧
        IntegrableOn (fun t => ∫ ω, K m t ω * K l t ω ∂P)
          (Ioo (0 : ℝ) (n : ℝ)) volume  := by
  intro k ρ hρstop hρle δ hδ hFloor A hA j
  intro L K
  intro m l
  obtain ⟨B, hB0, hG⟩ :=
    avram_gbB53_original_finitecap_postpayment_gradient_grid_regular
      X q hq w C hC hFiniteCap hw_smooth x D hD n hn
      ρ hρstop δ hδ j
  let G : ℕ → ℕ → Ω → ℝ := fun r i ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((r + 1 : ℕ) : ℝ≥0)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let a : ℝ := δ / 2
    let b : ℝ := C.toReal *
      (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let Y : ℝ := x + X.X s ω - rightLimit D s ω
    if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
      (if Y ∈ Icc a b then deriv w Y else 1)
    else 0
  let lo : ℕ → ℕ → ℝ := fun r i =>
    (((i : ℝ≥0) * ((n : ℝ≥0) / ((r + 1 : ℕ) : ℝ≥0))) : ℝ)
  let hi : ℕ → ℕ → ℝ := fun r i =>
    ((((i : ℝ≥0) * ((n : ℝ≥0) / ((r + 1 : ℕ) : ℝ≥0))) +
      ((n : ℝ≥0) / ((r + 1 : ℕ) : ℝ≥0))) : ℝ)
  letI : IsProbabilityMeasure P := X.isProbability
  have hstep :=
    avram_gb95_finite_step_pair_L2_time_integrable P (n : ℝ)
      (Finset.range (m + 1)) (Finset.range (l + 1))
      (lo m) (hi m) (lo l) (hi l) (G m) (G l)
      (by intro i hi; exact (hG m i).1)
      (by intro i hi; exact (hG l i).1)
      ⟨B, hB0, by intro i hi ω; exact (hG m i).2 ω⟩
      ⟨B, hB0, by intro i hi ω; exact (hG l i).2 ω⟩
  simpa [K, G, lo, hi] using hstep
