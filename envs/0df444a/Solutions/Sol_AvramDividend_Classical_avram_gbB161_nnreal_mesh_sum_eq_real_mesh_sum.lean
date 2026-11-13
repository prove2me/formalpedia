-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB161_nnreal_mesh_sum_eq_real_mesh_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:46:01.861067+00:00
-- url     : https://prove2.me/submissions/52d8838f-5426-4cbc-8123-fe064400b33b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB146_uniform_real_mesh_sum_bound_on_cells
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    (n m : ℕ) (t : ℝ) (c : ℕ → ℝ) :
    let Δnn : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let Δr : ℝ := (n : ℝ) / ((m : ℝ) + 1)
    (Finset.range (m + 1)).sum (fun i =>
      if (((i : ℝ≥0) * Δnn : ℝ≥0) : ℝ) ≤ t ∧
          t < ((((i : ℝ≥0) * Δnn) + Δnn : ℝ≥0) : ℝ)
      then c i else 0) =
    (Finset.range (m + 1)).sum (fun i =>
      if (i : ℝ) * Δr ≤ t ∧
          t < (((i + 1 : ℕ) : ℝ) * Δr)
      then c i else 0) := by
  intro Δnn Δr
  have hΔ : (Δnn : ℝ) = Δr := by
    simp only [Δnn, Δr, NNReal.coe_div, NNReal.coe_natCast,
      NNReal.coe_add, NNReal.coe_one, Nat.cast_add, Nat.cast_one]
  have hlo (i : ℕ) :
      (((i : ℝ≥0) * Δnn : ℝ≥0) : ℝ) = (i : ℝ) * Δr := by
    simp only [NNReal.coe_mul, NNReal.coe_natCast, hΔ]
  have hhi (i : ℕ) :
      ((((i : ℝ≥0) * Δnn) + Δnn : ℝ≥0) : ℝ) =
        (((i + 1 : ℕ) : ℝ) * Δr) := by
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast,
      hΔ, NNReal.coe_one, Nat.cast_add, Nat.cast_one]
    ring
  apply Finset.sum_congr rfl
  intro i hi
  rw [hlo i, hhi i]
