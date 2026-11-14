-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a90_original_stop_crossing_gaussian_spatial_generator_residual_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:22:05.235449+00:00
-- url     : https://prove2.me/submissions/e2e935db-4ae3-4cf7-b368-a19beb311df2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a72_original_gaussian_crossing_cell_clipped_endpoint_eq_stopped_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- The unique actual stopping-crossing Gaussian cell has a true stopped source endpoint and the original un-clipped Gaussian compensator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (ω : Ω) (n m i : ℕ) (ρ : ℝ≥0)
    (hstart : let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i : ℝ≥0) * Δ < ρ)
    (hend : let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ρ ≤ (i : ℝ≥0) * Δ + Δ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let Z : ℝ := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
    E (v (i + 1)) *
      (w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
        w (Y (v i))) -
      (if s < ρ then E s * (deriv w (Y s) * Z +
        (iteratedDeriv 2 w (Y s) / 2) *
          (Z^2 - (Δ : ℝ) * X.σ^2)) else 0) -
      (if s < ρ then (Δ : ℝ) * E s * X.generator w (Y s) else 0)
      =
    E ρ * (w (Y s + (X.X ρ ω - X.X s ω)) - w (Y s)) -
      E s * (deriv w (Y s) * Z +
        (iteratedDeriv 2 w (Y s) / 2) *
          (Z^2 - (Δ : ℝ) * X.σ^2)) -
      (Δ : ℝ) * E s * X.generator w (Y s) := by
  obtain ⟨hv0,hv1,_⟩ :=
    avram_ga_a72_original_gaussian_crossing_cell_clipped_endpoint_eq_stopped_source
      X x D ω n m i ρ hstart hend
  dsimp only at hv0 hv1 hstart
  dsimp only
  rw [hv0, hv1]
  simp only [if_pos hstart]
  have hSpatial :
      x + X.X ρ ω -
        rightLimit D ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω =
      (x + X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
        rightLimit D ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω) +
      (X.X ρ ω -
        X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω) := by
    ring
  rw [hSpatial]
