-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a48_masked_two_part_positive_L1_glue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T18:33:08.073316+00:00
-- url     : https://prove2.me/submissions/ed35b981-f05c-42e1-a55c-0c51fc304f3e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a26_positive_l1_two_term_glue
import Theorems.Thm_AvramDividend_Classical_avram_ga_a50_mask_zero_clock_unmask
import Theorems.Thm_AvramDividend_Classical_avram_ga_a51_mask_add_preserves_split
import Theorems.Thm_AvramDividend_Classical_avram_ga_a52_positive_part_mask
import Theorems.Thm_AvramDividend_Classical_avram_ga_a53_masked_positive_L1_transfer
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ρ : Ω → ℝ≥0) (B U V : ℕ → Ω → ℝ)
    (hSplit : ∀ m ω, B m ω = U m ω + V m ω)
    (hZero : ∀ m ω, ρ ω = 0 → B m ω = 0)
    (hI : ∀ m, Integrable (fun ω =>
      if 0 < ρ ω then max (B m ω) (0 : ℝ) else 0) P)
    (hU : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => if 0 < ρ ω then max (U m ω) (0 : ℝ) else 0) P ∧
      (∫ ω, (if 0 < ρ ω then max (U m ω) (0 : ℝ) else 0) ∂P) ≤ ε)
    (hV : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => if 0 < ρ ω then max (V m ω) (0 : ℝ) else 0) P ∧
      (∫ ω, (if 0 < ρ ω then max (V m ω) (0 : ℝ) else 0) ∂P) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (B m ω) (0 : ℝ)) P ∧
      (∫ ω, max (B m ω) (0 : ℝ) ∂P) ≤ ε := by
  let F : ℕ → Ω → ℝ :=
    fun m ω => if 0 < ρ ω then B m ω else 0
  let A : ℕ → Ω → ℝ :=
    fun m ω => if 0 < ρ ω then U m ω else 0
  let T : ℕ → Ω → ℝ :=
    fun m ω => if 0 < ρ ω then V m ω else 0
  have hAB : ∀ m ω, F m ω = A m ω + T m ω := by
    intro m ω
    exact avram_ga_a51_mask_add_preserves_split ρ B U V hSplit m ω
  have hIF : ∀ m, Integrable (fun ω => max (F m ω) (0 : ℝ)) P := by
    intro m
    change Integrable (fun ω => max
      (if 0 < ρ ω then B m ω else 0) (0 : ℝ)) P
    rw [avram_ga_a52_positive_part_mask ρ B m]
    exact hI m
  have hA := avram_ga_a53_masked_positive_L1_transfer P ρ U hU
  have hT := avram_ga_a53_masked_positive_L1_transfer P ρ V hV
  have hL1 := avram_ga_a26_positive_l1_two_term_glue P F A T hAB hIF hA hT
  have hFid : F = B := avram_ga_a50_mask_zero_clock_unmask ρ B hZero
  simpa only [hFid] using hL1
