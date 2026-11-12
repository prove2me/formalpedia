-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB91_one_mesh_step_indicator_refinement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:49:04.212866+00:00
-- url     : https://prove2.me/submissions/23f2bf09-0c16-4033-8b5a-64b4a77977d8

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Theorems.Thm_AvramDividend_Classical_avram_gbB93_coarse_cell_indicator_fine_block_partition
import Theorems.Thm_AvramDividend_Classical_avram_gbB94_finite_range_block_reindex
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} (n m b : ℕ) (hn : 0 < n) (hb : 0 < b)
    (G : ℕ → Ω → ℝ) :
    let D : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let δ : ℝ := (n : ℝ) / (((m + 1) * b : ℕ) : ℝ)
    ∀ t ∈ Ioo (0 : ℝ) (n : ℝ), ∀ ω : Ω,
      (Finset.range (m + 1)).sum (fun i =>
        if (((i : ℝ≥0) * D) : ℝ) ≤ t ∧
          t < ((((i : ℝ≥0) * D) + D : ℝ≥0) : ℝ)
        then G i ω else 0) =
      (Finset.range ((m + 1) * b)).sum (fun r =>
        if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
        then G (r / b) ω else 0) := by
  intro D δ t ht ω
  have hstep (i : ℕ) :
      (if (((i : ℝ≥0) * D) : ℝ) ≤ t ∧
        t < ((((i : ℝ≥0) * D) + D : ℝ≥0) : ℝ)
       then G i ω else 0) =
      (Finset.range b).sum (fun j =>
        if ((i * b + j : ℕ) : ℝ) * δ ≤ t ∧
          t < ((i * b + j + 1 : ℕ) : ℝ) * δ
        then G i ω else 0) := by
    have hcell :=
      AvramDividend.Classical.avram_gbB93_coarse_cell_indicator_fine_block_partition
        n m b i hn hb t
    calc
      _ = G i ω * (if (((i : ℝ≥0) * D) : ℝ) ≤ t ∧
          t < ((((i : ℝ≥0) * D) + D : ℝ≥0) : ℝ)
          then (1 : ℝ) else 0) := by split_ifs <;> ring
      _ = G i ω * (Finset.range b).sum (fun j =>
          if ((i * b + j : ℕ) : ℝ) * δ ≤ t ∧
            t < ((i * b + j + 1 : ℕ) : ℝ) * δ
          then (1 : ℝ) else 0) := by rw [hcell]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        split_ifs <;> ring
  calc
    _ = (Finset.range (m + 1)).sum (fun i =>
        (Finset.range b).sum (fun j =>
          if ((i * b + j : ℕ) : ℝ) * δ ≤ t ∧
            t < ((i * b + j + 1 : ℕ) : ℝ) * δ
          then G i ω else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hstep i
    _ = _ := by
      exact AvramDividend.Classical.avram_gbB94_finite_range_block_reindex
        (m + 1) b hb (fun i r =>
          if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
          then G i ω else 0)
