-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger175_original_zerojump_spatial_cell_error_expansion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:57:45.88189+00:00
-- url     : https://prove2.me/submissions/1e8bbc6d-ae5d-4371-a309-4d2a8510cf60

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger138_original_zerojump_physical_discounted_generator_Taylor_cell_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω) (s t : ℝ≥0) :
    let δ : ℝ := ((t - s : ℝ≥0) : ℝ)
    let E : ℝ := Real.exp (-(q * (s : ℝ)))
    let F : ℝ := Real.exp (-(q * (t : ℝ)))
    let y : ℝ := x + X.X s ω - rightLimit D s ω
    let Z : ℝ := x + X.X t ω - rightLimit D s ω
    let z : ℝ := X.X t ω - X.X s ω - δ * X.c
    F * (w Z - w y) -
      E * (deriv w y * z +
        (iteratedDeriv 2 w y / 2) * (z ^ 2 - δ * X.σ ^ 2)) -
      δ * E * (X.generator w y) =
    (F - E) * (w Z - w y) +
      E * (w Z - w y - deriv w y * (z + X.c * δ) -
        (iteratedDeriv 2 w y / 2) * (z + X.c * δ) ^ 2) +
      E * iteratedDeriv 2 w y * (X.c * δ * z + X.c ^ 2 * δ ^ 2 / 2) := by
  dsimp only
  have hcell :=
    avram_gledger138_original_zerojump_physical_discounted_generator_Taylor_cell_identity
      X hν x D w q ω s t
  dsimp only at hcell
  linear_combination hcell
