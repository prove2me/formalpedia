-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB58_original_finitecap_predictable_G_measurable_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:03:02.206814+00:00
-- url     : https://prove2.me/submissions/585b2fc6-82e9-4650-88ed-6ca483b6f018

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB59_original_finitecap_predictable_G_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gbB60_finitecap_clipped_gradient_uniform_bound
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Combine original-process gradient measurability with uniform
compact-band derivative bounds cell by cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (ρ : Ω → ℝ≥0)
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
      Measurable (G m i) ∧ ∀ ω, |G m i ω| ≤ B := by
  intro G
  obtain ⟨B, hB, hBu⟩ :=
    avram_gbB60_finitecap_clipped_gradient_uniform_bound
      (Ω := Ω) q hq w C hC hFiniteCap hw_smooth δ hδ j
  refine ⟨B, hB, ?_⟩
  intro m i
  constructor
  · exact avram_gbB59_original_finitecap_predictable_G_measurable
      X hX q hq w C hC hFiniteCap hw_smooth
      x D hD n hn ρ hρstop δ hδ j m i
  · intro ω
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let Y : Ω → ℝ := fun η => x + X.X s η - rightLimit D s η
    simpa only [G, Y, s, Δ] using hBu s ρ Y ω
