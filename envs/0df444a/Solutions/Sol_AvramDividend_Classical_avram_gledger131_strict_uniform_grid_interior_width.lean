-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger131_strict_uniform_grid_interior_width
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:57:25.055016+00:00
-- url     : https://prove2.me/submissions/43ea083a-0412-4f38-8585-14c9bea473e1

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    (n m : ℕ) (ρ : ℝ≥0) (k : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    (∀ i : ℕ, i < k → v (i + 1) < ρ) →
      ∀ i : ℕ, i < k →
        (v (i + 1) : ℝ) - (v i : ℝ) = (Δ : ℝ) := by
  dsimp only
  intro hstrict i hi
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
  let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
  have hnext : ((i + 1 : ℕ) : ℝ≥0) * Δ < ρ := by
    simpa only [v, min_lt_iff, lt_irrefl, or_false] using hstrict i hi
  have hprev : (i : ℝ≥0) * Δ ≤ ((i + 1 : ℕ) : ℝ≥0) * Δ := by
    gcongr
    omega
  have hiv : v i = (i : ℝ≥0) * Δ :=
    min_eq_left (le_trans hprev (le_of_lt hnext))
  have hnextv : v (i + 1) = ((i + 1 : ℕ) : ℝ≥0) * Δ :=
    min_eq_left (le_of_lt hnext)
  change (v (i + 1) : ℝ) - (v i : ℝ) = (Δ : ℝ)
  rw [hiv, hnextv]
  push_cast
  ring
