-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb88_single_block_original_time_ledger
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:41:08.508788+00:00
-- url     : https://prove2.me/submissions/46adbc18-c87b-436c-9cd3-6d624328f89b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb86_uniform_refinement_nnreal_time_bridge
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical
open scoped NNReal

/-- A centred coarse cell is one drift-corrected refined block. -/
theorem solution (n m b i : ℕ) (hb : 0 < b)
    (x : ℝ≥0 → ℝ) (c : ℝ) :
    let D : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let d : ℝ≥0 := (n : ℝ≥0) / (((m + 1) * b : ℕ) : ℝ≥0)
    let f : ℕ → ℝ := fun r => x ((r : ℝ≥0) * d) - (r : ℝ) * (d : ℝ) * c
    x ((i : ℝ≥0) * D + D) - x ((i : ℝ≥0) * D) - (D : ℝ) * c =
      f ((i + 1) * b) - f (i * b) := by
  dsimp only
  let D : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
  let d : ℝ≥0 := (n : ℝ≥0) / (((m + 1) * b : ℕ) : ℝ≥0)
  have ht (k : ℕ) : (k : ℝ≥0) * D = ((k * b : ℕ) : ℝ≥0) * d := by
    simpa [D, d] using
      (avram_gb86_uniform_refinement_nnreal_time_bridge n m b k hb)
  have hd : D = (b : ℝ≥0) * d := by
    simpa [D, d] using (ht 1)
  have hdr : (D : ℝ) = (b : ℝ) * (d : ℝ) := by
    exact_mod_cast hd
  have hs : (i : ℝ≥0) * D + D =
      (((i + 1) * b : ℕ) : ℝ≥0) * d := by
    calc
      _ = ((i + 1 : ℕ) : ℝ≥0) * D := by push_cast; ring
      _ = _ := ht (i + 1)
  rw [hs, ht i]
  change
    x ((((i + 1) * b : ℕ) : ℝ≥0) * d) -
        x (((i * b : ℕ) : ℝ≥0) * d) - (D : ℝ) * c =
      (x ((((i + 1) * b : ℕ) : ℝ≥0) * d) -
        (((i + 1) * b : ℕ) : ℝ) * (d : ℝ) * c) -
      (x (((i * b : ℕ) : ℝ≥0) * d) -
        ((i * b : ℕ) : ℝ) * (d : ℝ) * c)
  rw [hdr]
  push_cast
  ring
