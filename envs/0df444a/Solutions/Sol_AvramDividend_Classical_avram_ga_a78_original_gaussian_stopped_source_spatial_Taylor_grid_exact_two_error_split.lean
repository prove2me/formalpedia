-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a78_original_gaussian_stopped_source_spatial_Taylor_grid_exact_two_error_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:50:23.46697+00:00
-- url     : https://prove2.me/submissions/fbe2d619-03e4-497b-8932-d61be91d0788

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a77_original_gaussian_source_classical_spatial_Taylor_exact_cell_error
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The stopped original physical Gaussian source spatial generator error splits exactly into classical C2 Taylor and raw-centred drift cross errors. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ)
    (ρ : Ω → ℝ≥0) (ω : Ω) (S : Finset ℕ)
    (s : ℕ → ℝ≥0) (Δ : ℝ≥0) :
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℕ → ℝ := fun i =>
      x + X.X (s i) ω - rightLimit D (s i) ω
    let R : ℕ → ℝ := fun i =>
      X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    (∑ i ∈ S, if s i < ρ ω then
      E (s i) * (w (Y i + R i) - w (Y i) -
        (deriv w (Y i) * Z i +
          (iteratedDeriv 2 w (Y i) / 2) *
            (Z i^2 - (Δ : ℝ) * X.σ^2)) -
        (Δ : ℝ) * X.generator w (Y i))
      else 0) =
    (∑ i ∈ S, if s i < ρ ω then
      E (s i) * (w (Y i + R i) - w (Y i) -
        deriv w (Y i) * R i -
        (iteratedDeriv 2 w (Y i) / 2) * R i^2)
      else 0) +
    (∑ i ∈ S, if s i < ρ ω then
      E (s i) * (iteratedDeriv 2 w (Y i) / 2) *
        (R i^2 - Z i^2)
      else 0) := by
  classical
  dsimp
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : s i < ρ ω
  · simp only [if_pos h]
    simpa only [mul_add] using
      (avram_ga_a77_original_gaussian_source_classical_spatial_Taylor_exact_cell_error
        X hν x D w q ω (s i) Δ)
  · simp only [if_neg h, zero_add]
