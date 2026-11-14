-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a88_original_fullcell_clipped_source_discount_difference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:22:05.133243+00:00
-- url     : https://prove2.me/submissions/d2175e3f-af48-4804-a899-118d2c9b2e02

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a71_original_gaussian_fullcell_clipped_spatial_endpoint_eq_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- On a complete original Gaussian pre-stop physical cell, the clipped-vs-unclipped source spatial value error consists exactly of the discount difference. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (ω : Ω) (n m i : ℕ) (ρ : ℝ≥0)
    (hs : let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i : ℝ≥0) * Δ < ρ)
    (hfull : let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i : ℝ≥0) * Δ + Δ ≤ ρ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let y : ℝ := x + X.X s ω - rightLimit D s ω
    let r : ℝ := X.X (s + Δ) ω - X.X s ω
    E (v (i + 1)) *
      (w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
        w (x + X.X (v i) ω - rightLimit D (v i) ω)) -
      E s * (w (y + r) - w y) =
      (E (s + Δ) - E s) * (w (y + r) - w y) := by
  obtain ⟨hv0,hv1,_⟩ :=
    avram_ga_a71_original_gaussian_fullcell_clipped_spatial_endpoint_eq_source
      X x D ω n m i ρ hfull
  dsimp only at hv0 hv1
  dsimp only
  rw [hv0, hv1]
  have hSpatial :
      x + X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) +
        (n : ℝ≥0) / ((m : ℝ≥0) + 1)) ω -
        rightLimit D ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω =
      (x + X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
        rightLimit D ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω) +
      (X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) +
        (n : ℝ≥0) / ((m : ℝ≥0) + 1)) ω -
        X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω) := by
    ring
  rw [hSpatial]
  ring
