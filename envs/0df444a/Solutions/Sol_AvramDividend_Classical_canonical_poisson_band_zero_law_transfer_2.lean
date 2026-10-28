-- Prove2me | solution 2 for AvramDividend.Classical.canonical_poisson_band_zero_law_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:48:18.758582+00:00
-- url     : https://prove2.me/submissions/0fa6da7b-50e4-424c-a7c5-3e50cfd7d0fb

import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_cross_levy_path_event_law_of_equal_psi

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Poisson zero-count probabilities transfer through equality of measurable Lévy path laws. -/
theorem solution
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hψ : ∀ θ : ℝ, 0 < θ → X.ψ θ = Y.ψ θ)
    (δ : ℕ → ℝ≥0)
    (count : ℕ → ℕ → (ℝ≥0 → ℝ) → ℕ)
    (hcount : ∀ k n, Measurable (count k n))
    (hcanonical : ∀ k n,
      P₂ {ω | count k n (fun t : ℝ≥0 => Y.X t ω) = 0} =
      ENNReal.ofReal (Real.exp
        (-((δ k : ℝ) *
          (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)))) :
    ∀ k n,
      P₁ {ω | count k n (fun t : ℝ≥0 => X.X t ω) = 0} =
      ENNReal.ofReal (Real.exp
        (-((δ k : ℝ) *
          (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal))) := by
  intro k n
  have hE : MeasurableSet {f : ℝ≥0 → ℝ | count k n f = 0} :=
    (measurableSet_singleton (0 : ℕ)).preimage (hcount k n)
  have htransfer :=
    cross_levy_path_event_law_of_equal_psi X Y hψ
      {f : ℝ≥0 → ℝ | count k n f = 0} hE
  exact htransfer.trans (hcanonical k n)
