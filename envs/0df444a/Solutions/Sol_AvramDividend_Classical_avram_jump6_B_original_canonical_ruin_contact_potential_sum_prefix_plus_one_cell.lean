-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_canonical_ruin_contact_potential_sum_prefix_plus_one_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:02:11.649732+00:00
-- url     : https://prove2.me/submissions/a57874ad-5eed-4008-b29b-cfc30d6f037b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_canonical_grid_after_crossing_identically_stopped
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (w : ℝ → ℝ)
    (n j i : ℕ) (ρ : ℝ≥0) (hρn : ρ ≤ (n : ℝ≥0))
    (hi : i < (n + 1) * (j + 1))
    (hcross : min (((i + 1 : ℕ) : ℝ≥0) /
        ((j + 1 : ℕ) : ℝ≥0)) ρ = ρ) :
    let v : ℕ → ℝ≥0 := fun l =>
      min ((l : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun l =>
      x + X.X (v (l + 1)) ω - rightLimit D (v l) ω
    (∑ l ∈ Finset.range ((n + 1) * (j + 1)),
      E (v (l + 1)) * (w (Y (v (l + 1))) - w (Z l))) =
      (∑ l ∈ Finset.range i,
        E (v (l + 1)) * (w (Y (v (l + 1))) - w (Z l))) +
      E ρ * (w (Y ρ) - w (Z i)) := by
  let m : ℕ := (n + 1) * (j + 1)
  let v : ℕ → ℝ≥0 := fun l =>
    min ((l : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
  let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
  let Z : ℕ → ℝ := fun l =>
    x + X.X (v (l + 1)) ω - rightLimit D (v l) ω
  let f : ℕ → ℝ := fun l => E (v (l + 1)) *
    (w (Y (v (l + 1))) - w (Z l))
  have hstop (l : ℕ) (hl : i + 1 ≤ l) : v l = ρ :=
    avram_jump6_B_actual_canonical_grid_after_crossing_identically_stopped
      n j ρ hρn (i + 1) hcross l hl
  have hzero (l : ℕ) (hl : i + 1 ≤ l) : f l = 0 := by
    have hl0 := hstop l hl
    have hl1 := hstop (l + 1) (by omega)
    dsimp [f, Y, Z]
    rw [hl0, hl1]
    ring
  have him : i + 1 ≤ m := by omega
  have hsum :
      (∑ l ∈ Finset.range m, f l) =
      (∑ l ∈ Finset.range i, f l) + f i := by
    calc
      (∑ l ∈ Finset.range m, f l) =
          (∑ l ∈ Finset.range (i + 1), f l) +
          (∑ l ∈ Finset.range (m - (i + 1)), f (i + 1 + l)) := by
            simpa only [Nat.add_sub_of_le him] using
              (Finset.sum_range_add f (i + 1) (m - (i + 1)))
      _ = (∑ l ∈ Finset.range (i + 1), f l) := by
            simp [hzero]
      _ = (∑ l ∈ Finset.range i, f l) + f i := by
            rw [Finset.sum_range_succ]
  change (∑ l ∈ Finset.range m, f l) =
      (∑ l ∈ Finset.range i, f l) +
      E ρ * (w (Y ρ) - w (Z i))
  rw [hsum]
  congr 1
  change E (v (i + 1)) * (w (Y (v (i + 1))) - w (Z i)) =
    E ρ * (w (Y ρ) - w (Z i))
  have hv : v (i + 1) = ρ := hcross
  rw [hv]
