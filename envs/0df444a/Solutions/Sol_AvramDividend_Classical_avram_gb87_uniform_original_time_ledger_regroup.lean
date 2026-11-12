-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb87_uniform_original_time_ledger_regroup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:29:30.515199+00:00
-- url     : https://prove2.me/submissions/b3101ce3-355e-45ce-a53c-543c94870ab4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb83_weighted_block_refinement
import Theorems.Thm_AvramDividend_Classical_avram_gb86_uniform_refinement_nnreal_time_bridge
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal BigOperators

theorem solution
    (n m b : ℕ) (hb : 0 < b) (x : ℝ≥0 → ℝ) (c : ℝ) (g : ℕ → ℝ) :
    let D : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let d : ℝ≥0 := (n : ℝ≥0) / (((m + 1) * b : ℕ) : ℝ≥0)
    (Finset.range (m + 1)).sum (fun i =>
      g i * (x ((i : ℝ≥0) * D + D) - x ((i : ℝ≥0) * D) - (D : ℝ) * c)) =
    (Finset.range ((m + 1) * b)).sum (fun r =>
      g (r / b) * (x ((r : ℝ≥0) * d + d) - x ((r : ℝ≥0) * d) - (d : ℝ) * c)) := by
  classical
  dsimp only
  let D : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
  let d : ℝ≥0 := (n : ℝ≥0) / (((m + 1) * b : ℕ) : ℝ≥0)
  let s : ℕ → ℝ≥0 := fun r => (r : ℝ≥0) * d
  let f : ℕ → ℝ := fun r => x (s r) - (s r : ℝ) * c
  have halign (i : ℕ) : (i : ℝ≥0) * D = s (i * b) := by
    exact avram_gb86_uniform_refinement_nnreal_time_bridge n m b i hb
  have hstep (r : ℕ) : f (r + 1) - f r =
      x (s r + d) - x (s r) - (d : ℝ) * c := by
    have hs : s (r + 1) = s r + d := by
      simp only [s, Nat.cast_add, Nat.cast_one]
      ring
    simp only [f, hs]
    push_cast
    ring
  have hcoarse (i : ℕ) :
      f ((i + 1) * b) - f (i * b) =
      x ((i : ℝ≥0) * D + D) - x ((i : ℝ≥0) * D) - (D : ℝ) * c := by
    change x (s ((i + 1) * b)) - (s ((i + 1) * b) : ℝ) * c -
      (x (s (i * b)) - (s (i * b) : ℝ) * c) = _
    rw [← halign (i + 1), ← halign i]
    push_cast
    ring
  calc
    (Finset.range (m + 1)).sum (fun i =>
      g i * (x ((i : ℝ≥0) * D + D) - x ((i : ℝ≥0) * D) - (D : ℝ) * c)) =
        (Finset.range (m + 1)).sum (fun i =>
          g i * (f ((i + 1) * b) - f (i * b))) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hcoarse i]
    _ = (Finset.range ((m + 1) * b)).sum (fun r =>
      g (r / b) * (f (r + 1) - f r)) :=
        avram_gb83_weighted_block_refinement m b hb f g
    _ = (Finset.range ((m + 1) * b)).sum (fun r =>
      g (r / b) * (x ((r : ℝ≥0) * d + d) - x ((r : ℝ≥0) * d) -
        (d : ℝ) * c)) := by
          apply Finset.sum_congr rfl
          intro r hr
          simp only [hstep, s]
