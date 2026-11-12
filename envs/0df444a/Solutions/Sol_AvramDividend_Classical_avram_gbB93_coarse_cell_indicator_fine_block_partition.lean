-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB93_coarse_cell_indicator_fine_block_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T21:51:40.484205+00:00
-- url     : https://prove2.me/submissions/063722e2-a3c0-41a5-84f4-1809c816b19c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB94_monotone_step_indicator_telescope
import Theorems.Thm_AvramDividend_Classical_avram_gbB95_product_refinement_endpoint_equalities
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

theorem solution
    (n m b i : ℕ) (hn : 0 < n) (hb : 0 < b) (t : ℝ) :
    let D : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let δ : ℝ := (n : ℝ) / (((m + 1) * b : ℕ) : ℝ)
    (if (((i : ℝ≥0) * D) : ℝ) ≤ t ∧
      t < ((((i : ℝ≥0) * D) + D : ℝ≥0) : ℝ)
     then (1 : ℝ) else 0) =
    (Finset.range b).sum (fun j =>
      if ((i * b + j : ℕ) : ℝ) * δ ≤ t ∧
        t < ((i * b + j + 1 : ℕ) : ℝ) * δ
      then (1 : ℝ) else 0) := by
  intro D δ
  obtain ⟨hl, hr⟩ :=
    avram_gbB95_product_refinement_endpoint_equalities n m b i hn hb
  let f : ℕ → ℝ := fun j => ((i * b + j : ℕ) : ℝ) * δ
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hf : Monotone f := by
    intro j k hjk
    dsimp [f]
    apply mul_le_mul_of_nonneg_right _ hδ
    exact_mod_cast Nat.add_le_add_left hjk (i * b)
  have hFine := avram_gbB94_monotone_step_indicator_telescope f hf t b
  let a : ℝ := ((((i : ℝ≥0) * D) : ℝ))
  let c : ℝ := (((((i : ℝ≥0) * D) + D : ℝ≥0) : ℝ))
  have hac : a ≤ c := by
    dsimp [a, c]
    exact_mod_cast (le_add_of_nonneg_right D.property :
      (i : ℝ≥0) * D ≤ (i : ℝ≥0) * D + D)
  have ha : a = f 0 := by
    simpa only [a, f, Nat.add_zero] using hl
  have hc : c = f b := by
    simpa only [c, f] using hr
  have hStep :
      (if a ≤ t ∧ t < c then (1 : ℝ) else 0) =
        (if a ≤ t then (1 : ℝ) else 0) -
          (if c ≤ t then (1 : ℝ) else 0) := by
    by_cases h₁ : a ≤ t
    · by_cases h₂ : t < c
      · simp [h₁, h₂, not_le.mpr h₂]
      · have h₂' : c ≤ t := le_of_not_gt h₂
        simp [h₁, h₂, h₂']
    · have h₂ : ¬ c ≤ t := fun h => h₁ (hac.trans h)
      simp [h₁, h₂]
  calc
    _ = (if a ≤ t then (1 : ℝ) else 0) -
          (if c ≤ t then (1 : ℝ) else 0) := by
      simpa only [a, c] using hStep
    _ = (if f 0 ≤ t then (1 : ℝ) else 0) -
          (if f b ≤ t then (1 : ℝ) else 0) := by
      rw [ha, hc]
    _ = _ := by
      simpa [f, Nat.add_assoc] using hFine.symm
