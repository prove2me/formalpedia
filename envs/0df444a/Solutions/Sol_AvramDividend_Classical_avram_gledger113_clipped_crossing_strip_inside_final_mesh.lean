-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger113_clipped_crossing_strip_inside_final_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:46:36.615641+00:00
-- url     : https://prove2.me/submissions/01590e0b-0df5-4223-995a-def5fd85b327

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
noncomputable section

/-- The unique clipped crossing cell is contained in the final
    real-subtracted open strip, with no terminal endpoint atom. -/
theorem solution
    (n m k : ℕ) (ρ : ℝ≥0) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    v k < ρ → v (k + 1) = ρ →
      Ioo (v k : ℝ) (ρ : ℝ) ⊆
        Ioo ((ρ : ℝ) - (Δ : ℝ)) (ρ : ℝ) := by
  dsimp only
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
  let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
  intro hvk hstop
  have hleft : (k : ℝ≥0) * Δ < ρ := by
    by_contra hneg
    have hρle : ρ ≤ (k : ℝ≥0) * Δ := le_of_not_gt hneg
    have heq : v k = ρ := by
      dsimp [v]
      exact min_eq_right hρle
    exact (ne_of_lt hvk) heq
  have hvk_eq : v k = (k : ℝ≥0) * Δ := by
    dsimp [v]
    exact min_eq_left (le_of_lt hleft)
  have hright : ρ ≤ ((k + 1 : ℕ) : ℝ≥0) * Δ := by
    have hmin : min (((k + 1 : ℕ) : ℝ≥0) * Δ) ρ = ρ := hstop
    exact min_eq_right_iff.mp hmin
  have hmul :
      (((k + 1 : ℕ) : ℝ≥0) * Δ) = (k : ℝ≥0) * Δ + Δ := by
    push_cast
    ring
  have hnn : ρ ≤ v k + Δ := by
    calc
      ρ ≤ ((k + 1 : ℕ) : ℝ≥0) * Δ := hright
      _ = (k : ℝ≥0) * Δ + Δ := hmul
      _ = v k + Δ := by rw [hvk_eq]
  have hr : (ρ : ℝ) - (Δ : ℝ) ≤ (v k : ℝ) := by
    have hr' : (ρ : ℝ) ≤ (v k : ℝ) + (Δ : ℝ) := by
      exact_mod_cast hnn
    linarith
  intro t ht
  exact ⟨lt_of_le_of_lt hr ht.1, ht.2⟩
