-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB145_original_finitecap_step_K_bound_from_generic_clipped_gradient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T10:58:34.402568+00:00
-- url     : https://prove2.me/submissions/ad5805a9-23de-4032-bea3-38a0659b15eb

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB60_finitecap_clipped_gradient_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_gb99_finite_step_abs_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
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
    let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (m + 1)).sum (fun i =>
        if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ)
        then G m i ω else 0)
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m t ω, |K m t ω| ≤ (m + 1 : ℕ) * B := by
  intro G K
  rcases avram_gbB60_finitecap_clipped_gradient_uniform_bound
      (Ω := Ω) q hq w C hC hFiniteCap hw_smooth δ hδ j
    with ⟨B, hB, hb⟩
  refine ⟨B, hB, ?_⟩
  intro m t ω
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  have hc : ∀ i ∈ Finset.range (m + 1), ∀ η, |G m i η| ≤ B := by
    intro i hi η
    have h := hb (s i) ρ
      (fun η => x + X.X (s i) η - rightLimit D (s i) η) η
    simpa only [G, s, Δ] using h
  have hh := avram_gb99_finite_step_abs_bound
    (Finset.range (m + 1)) (fun i => (s i : ℝ))
    (fun i => ((s i + Δ : ℝ≥0) : ℝ))
    (G m) B hB hc t ω
  simpa only [K, Δ, s, Finset.card_range, Nat.cast_add, Nat.cast_one] using hh
