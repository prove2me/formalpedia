-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB53_original_finitecap_postpayment_gradient_grid_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:57:05.298278+00:00
-- url     : https://prove2.me/submissions/a54a24d1-985c-47db-a5c1-ae52783a6839

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB54_original_finitecap_gradient_band_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_gbB55_original_finitecap_postpayment_gradient_grid_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
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
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m i,
      StronglyMeasurable (G m i) ∧ ∀ ω, |G m i ω| ≤ B := by
  let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) /
    ((m + 1 : ℕ) : ℝ≥0)
  let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
  let Y : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    x + X.X (s m i) ω - rightLimit D (s m i) ω
  let G : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    if s m i < ρ ω then Real.exp (-(q * (s m i : ℝ))) *
      (if Y m i ω ∈ Icc (δ / 2)
        (C.toReal * (((j + 1 : ℕ) : ℝ) /
          ((j + 2 : ℕ) : ℝ))) then deriv w (Y m i ω) else 1)
    else 0
  change ∃ B : ℝ, 0 ≤ B ∧ ∀ m i,
    StronglyMeasurable (G m i) ∧ ∀ ω, |G m i ω| ≤ B
  obtain ⟨B, hB, hb⟩ :=
    avram_gbB54_original_finitecap_gradient_band_uniform_bound
      (Ω := Ω) q hq w C hC hFiniteCap hw_smooth δ hδ j
  refine ⟨B, hB, ?_⟩
  intro m i
  constructor
  · have hm : Measurable (G m i) := by
      simpa only [G, Y, s, Δ] using
        (avram_gbB55_original_finitecap_postpayment_gradient_grid_measurable
          X q hq w C hC hFiniteCap hw_smooth x D hD
          n hn ρ hρstop δ hδ j m i)
    exact hm.stronglyMeasurable
  · intro ω
    have hh := hb (s m i) ρ (Y m i) ω
    simpa only [G] using hh
