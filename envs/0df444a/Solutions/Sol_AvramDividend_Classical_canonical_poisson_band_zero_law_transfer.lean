-- Prove2me | solution 1 for AvramDividend.Classical.canonical_poisson_band_zero_law_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:48:03.56+00:00
-- url     : https://prove2.me/submissions/5053fa1e-17fb-42ec-9bbb-130781547b15

import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_cross_levy_path_event_law_of_equal_psi
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

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
  let E : Set (ℝ≥0 → ℝ) := {path | count k n path = 0}
  have hE : MeasurableSet E :=
    (measurableSet_singleton (0 : ℕ)).preimage (hcount k n)
  have hLaw := cross_levy_path_event_law_of_equal_psi X Y hψ E hE
  change P₁ {ω | count k n (fun t : ℝ≥0 => X.X t ω) = 0} =
    P₂ {ω | count k n (fun t : ℝ≥0 => Y.X t ω) = 0} at hLaw
  exact hLaw.trans (hcanonical k n)