-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB126_original_physical_postpayment_gradient_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:38:17.750422+00:00
-- url     : https://prove2.me/submissions/b039c6f5-37bb-44ac-ad0e-f1bea6c25eda

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB60_finitecap_clipped_gradient_uniform_bound
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
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ρ : Ω → ℝ≥0) (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    let H : ℝ≥0 → Ω → ℝ := fun s ω =>
      let a : ℝ := δ / 2
      let b : ℝ := C.toReal *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let Y : ℝ := x + X.X s ω - rightLimit D s ω
      if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
        (if Y ∈ Icc a b then deriv w Y else 1)
      else 0
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ω, |H s ω| ≤ B := by
  obtain ⟨B, hB, hBound⟩ :=
    avram_gbB60_finitecap_clipped_gradient_uniform_bound
      (Ω := Ω) q hq w C hC hFiniteCap hw_smooth δ hδ j
  refine ⟨B, hB, ?_⟩
  intro s ω
  let Y : Ω → ℝ := fun η =>
    x + X.X s η - rightLimit D s η
  simpa [Y] using (hBound s ρ Y ω)
