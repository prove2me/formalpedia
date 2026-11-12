-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a25_original_clipped_spatial_sum_expansion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:22:56.135545+00:00
-- url     : https://prove2.me/submissions/9ae0486a-e375-492f-990e-1bf623e4faf5

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger175_original_zerojump_spatial_cell_error_expansion
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (m n : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
    let L : ℝ≥0 → ℝ≥0 → ℝ := fun s t =>
      let δ : ℝ := ((t - s : ℝ≥0) : ℝ)
      let E : ℝ := Real.exp (-(q * (s : ℝ)))
      let F : ℝ := Real.exp (-(q * (t : ℝ)))
      let y : ℝ := x + X.X s ω - rightLimit D s ω
      let Z : ℝ := x + X.X t ω - rightLimit D s ω
      let z : ℝ := X.X t ω - X.X s ω - δ * X.c
      F * (w Z - w y) -
        E * (deriv w y * z +
          (iteratedDeriv 2 w y / 2) * (z ^ 2 - δ * X.σ ^ 2)) -
        δ * E * X.generator w y
    let R : ℝ≥0 → ℝ≥0 → ℝ := fun s t =>
      let δ : ℝ := ((t - s : ℝ≥0) : ℝ)
      let E : ℝ := Real.exp (-(q * (s : ℝ)))
      let F : ℝ := Real.exp (-(q * (t : ℝ)))
      let y : ℝ := x + X.X s ω - rightLimit D s ω
      let Z : ℝ := x + X.X t ω - rightLimit D s ω
      let z : ℝ := X.X t ω - X.X s ω - δ * X.c
      (F - E) * (w Z - w y) +
        E * (w Z - w y - deriv w y * (z + X.c * δ) -
          (iteratedDeriv 2 w y / 2) * (z + X.c * δ) ^ 2) +
        E * iteratedDeriv 2 w y * (X.c * δ * z + X.c ^ 2 * δ ^ 2 / 2)
    (∑ i ∈ Finset.range (m + 1), L (v i) (v (i + 1))) =
      ∑ i ∈ Finset.range (m + 1), R (v i) (v (i + 1)) := by
  dsimp only
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact avram_gledger175_original_zerojump_spatial_cell_error_expansion
    X hν x D w q ω _ _
