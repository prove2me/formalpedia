-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_clipped_crossing_strip_inside_nonnegative_final_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T00:01:57.525659+00:00
-- url     : https://prove2.me/submissions/5b6cc1a2-981d-438b-80da-c721514a73f7

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring


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
        Ioo ((ρ - Δ : ℝ≥0) : ℝ) (ρ : ℝ) := by
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
  have hsub : ρ - Δ ≤ v k := tsub_le_iff_right.mpr hnn
  have hr : ((ρ - Δ : ℝ≥0) : ℝ) ≤ (v k : ℝ) := by
    exact_mod_cast hsub
  intro t ht
  exact ⟨lt_of_le_of_lt hr ht.1, ht.2⟩
