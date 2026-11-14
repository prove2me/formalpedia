-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a77_original_gaussian_source_classical_spatial_Taylor_exact_cell_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:50:19.515906+00:00
-- url     : https://prove2.me/submissions/7e3c81a1-f7bd-4a7c-b9bd-cfe85db061d6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_zero_jump_generator_eq_gaussian_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual source-based full Gaussian Taylor and generator residual is exactly classical C2 remainder plus a raw-centred quadratic cross error. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ)
    (ω : Ω) (s Δ : ℝ≥0) :
    let E : ℝ := Real.exp (-(q * (s : ℝ)))
    let y : ℝ := x + X.X s ω - rightLimit D s ω
    let r : ℝ := X.X (s + Δ) ω - X.X s ω
    let z : ℝ := r - (Δ : ℝ) * X.c
    E * (w (y + r) - w y -
      (deriv w y * z +
        (iteratedDeriv 2 w y / 2) * (z^2 - (Δ : ℝ) * X.σ^2)) -
      (Δ : ℝ) * X.generator w y) =
    E * (w (y + r) - w y -
      deriv w y * r - (iteratedDeriv 2 w y / 2) * r^2) +
      E * (iteratedDeriv 2 w y / 2) * (r^2 - z^2) := by
  dsimp
  rw [avram_p4_f11_zero_jump_generator_eq_gaussian_drift X hν]
  ring
