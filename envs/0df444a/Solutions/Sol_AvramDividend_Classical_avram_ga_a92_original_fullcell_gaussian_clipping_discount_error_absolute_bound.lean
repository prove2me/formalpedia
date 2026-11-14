-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a92_original_fullcell_gaussian_clipping_discount_error_absolute_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:22:03.021202+00:00
-- url     : https://prove2.me/submissions/478065cb-a59d-4bc8-a202-c05a6b915357

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a88_original_fullcell_clipped_source_discount_difference
import Theorems.Thm_AvramDividend_Classical_avram_gledger147_clipped_final_discount_cell_absolute_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- The genuine original full pre-stop Gaussian clipped spatial discount mismatch is bounded by discount rate times physical width times absolute source value displacement. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hq : 0 ≤ q) (ω : Ω) (n m i : ℕ) (ρ : ℝ≥0)
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
    |E (v (i + 1)) *
      (w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
        w (x + X.X (v i) ω - rightLimit D (v i) ω)) -
      E s * (w (y + r) - w y)| ≤
      q * (Δ : ℝ) * |w (y + r) - w y| := by
  have heq :=
    avram_ga_a88_original_fullcell_clipped_source_discount_difference
      X x D w q ω n m i ρ hs hfull
  dsimp only at heq
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℝ≥0 := (i : ℝ≥0) * Δ
  have hdisc : |Real.exp (-(q * ((s + Δ : ℝ≥0) : ℝ))) -
      Real.exp (-(q * (s : ℝ)))| ≤ q * (Δ : ℝ) := by
    simpa only [NNReal.coe_add] using
      (avram_gledger147_clipped_final_discount_cell_absolute_bound
        q (s : ℝ) (Δ : ℝ) (Δ : ℝ) hq s.property Δ.property le_rfl)
  dsimp only
  rw [heq, abs_mul]
  exact mul_le_mul_of_nonneg_right hdisc (abs_nonneg _)
