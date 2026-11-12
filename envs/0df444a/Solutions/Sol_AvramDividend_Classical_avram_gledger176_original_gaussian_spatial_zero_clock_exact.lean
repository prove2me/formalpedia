-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger176_original_gaussian_spatial_zero_clock_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T23:11:36.512473+00:00
-- url     : https://prove2.me/submissions/970bc8af-6801-4d13-8fb4-d7c1f8c524cd

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (ρ : Ω → ℝ≥0) (ω : Ω) (hρ0 : ρ ω = 0) (n m : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    (∑ i ∈ Finset.range (m + 1),
      E (v (i + 1)) * (w (Z i) - w (Y (v i)))) -
    (∑ i ∈ Finset.range m,
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then
        let y := Y s
        let z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        E s * (deriv w y * z +
          (iteratedDeriv 2 w y / 2) * (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      else 0) -
    (∑ i ∈ Finset.range m,
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then (Δ : ℝ) * E s * X.generator w (Y s)
      else 0) = 0 := by
  dsimp only
  have hv : ∀ i : ℕ,
      min ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) (ρ ω) = 0 := by
    intro i
    rw [hρ0]
    apply min_eq_right
    positivity
  simp only [hv, hρ0]
  simp
