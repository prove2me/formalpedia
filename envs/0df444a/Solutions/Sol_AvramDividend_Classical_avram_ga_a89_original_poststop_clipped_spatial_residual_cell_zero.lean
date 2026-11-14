-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a89_original_poststop_clipped_spatial_residual_cell_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:22:04.068373+00:00
-- url     : https://prove2.me/submissions/88cf7619-b702-4d17-9e8b-030f9fa32a71

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Every actual post-stop Gaussian source cell has zero clipped spatial residual and zero source compensator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (ω : Ω) (n m i : ℕ) (ρ : ℝ≥0)
    (hpost : let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ρ ≤ (i : ℝ≥0) * Δ) :
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
      = 0 := by
  dsimp at hpost ⊢
  have h0 : min ((i : ℝ≥0) *
      ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ρ = ρ :=
    min_eq_right hpost
  have hi : (((i + 1 : ℕ) : ℝ≥0) *
      ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) =
      (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) +
        (n : ℝ≥0) / ((m : ℝ≥0) + 1) := by
    push_cast
    ring
  have h1 : min (((i + 1 : ℕ) : ℝ≥0) *
      ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ρ = ρ := by
    rw [hi]
    exact min_eq_right (le_trans hpost (le_add_of_nonneg_right (zero_le)))
  have hNot : ¬ (i : ℝ≥0) *
      ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ :=
    not_lt.mpr hpost
  simp only [h0, h1, if_neg hNot, sub_zero, sub_self, mul_zero]
