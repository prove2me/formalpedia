-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a57_original_clipped_gaussian_cell_width
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:24:14.908796+00:00
-- url     : https://prove2.me/submissions/0b87faf0-069c-4e62-961e-86f63e3274e9

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_clipped_source_cell_mesh_nonexpansive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    (n m i : ℕ) (ρ : ℝ≥0) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) ρ
    0 ≤ (v (i + 1) : ℝ) - (v i : ℝ) ∧
      (v (i + 1) : ℝ) - (v i : ℝ) ≤ (Δ : ℝ) := by
  intro Δ v
  let u : Nat -> ℝ≥0 := fun k => (k : ℝ≥0) * Δ
  have hu : Monotone u := by
    intro a b hab
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (by positivity)
  have hstep : u (i + 1) = u i + Δ := by
    simp [u, Nat.cast_add, Nat.cast_one, add_mul]
  have hd : ((u (i + 1) : ℝ) - (u i : ℝ)) = (Δ : ℝ) := by
    simp [hstep]
  have hv : v i ≤ v (i + 1) := by
    change min (u i) ρ ≤ min (u (i + 1)) ρ
    exact min_le_min_right ρ (hu (Nat.le_succ i))
  constructor
  · exact sub_nonneg.mpr (by exact_mod_cast hv)
  · have hb := avram_wave6_06_original_clipped_source_cell_mesh_nonexpansive
      u hu i ρ (Δ : ℝ) (by exact_mod_cast (by positivity)) (le_of_eq hd)
    exact hb
