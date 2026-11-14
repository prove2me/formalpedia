-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a128_original_gaussian_physical_source_full_cell_three_error_exact_algebra
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:13:26.170997+00:00
-- url     : https://prove2.me/submissions/4daa62a5-8587-4804-a980-3e769986a0cd

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a77_original_gaussian_source_classical_spatial_Taylor_exact_cell_error
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Original physical source Gaussian full cell splits exactly into compact Taylor, raw-centred Hessian and discount-Euler spatial errors. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω) (s Δ : ℝ≥0) :
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let y : ℝ := x + X.X s ω - rightLimit D s ω
    let r : ℝ := X.X (s + Δ) ω - X.X s ω
    let z : ℝ := r - (Δ : ℝ) * X.c
    let W : ℝ := w (y + r) - w y
    let Q : ℝ := deriv w y * z +
      (iteratedDeriv 2 w y / 2) * (z^2 - (Δ : ℝ) * X.σ^2)
    let T : ℝ := E s * (W - deriv w y * r -
      (iteratedDeriv 2 w y / 2) * r^2)
    let B : ℝ := E s * (iteratedDeriv 2 w y / 2) * (r^2 - z^2)
    let C : ℝ := (E (s + Δ) - E s) * W
    E (s + Δ) * W - E s * Q -
      (Δ : ℝ) * E s * X.generator w y = T + B + C := by
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
  let y : ℝ := x + X.X s ω - rightLimit D s ω
  let r : ℝ := X.X (s + Δ) ω - X.X s ω
  let z : ℝ := r - (Δ : ℝ) * X.c
  let W : ℝ := w (y + r) - w y
  let Q : ℝ := deriv w y * z +
    (iteratedDeriv 2 w y / 2) * (z^2 - (Δ : ℝ) * X.σ^2)
  let T : ℝ := E s * (W - deriv w y * r -
    (iteratedDeriv 2 w y / 2) * r^2)
  let B : ℝ := E s * (iteratedDeriv 2 w y / 2) * (r^2 - z^2)
  let C : ℝ := (E (s + Δ) - E s) * W
  change E (s + Δ) * W - E s * Q -
    (Δ : ℝ) * E s * X.generator w y = T + B + C
  have h77 := avram_ga_a77_original_gaussian_source_classical_spatial_Taylor_exact_cell_error
    X hν x D w q ω s Δ
  have h77' : E s * (W - Q) -
      (Δ : ℝ) * E s * X.generator w y = T + B := by
    dsimp only [E, y, r, z, W, Q, T, B] at *
    convert h77 using 1 <;> ring
  calc
    E (s + Δ) * W - E s * Q -
      (Δ : ℝ) * E s * X.generator w y =
      (E s * (W - Q) -
        (Δ : ℝ) * E s * X.generator w y) + C := by
        dsimp only [C]; ring
    _ = T + B + C := by rw [h77']
