-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a95_original_gaussian_uniform_mesh_true_crossing_card_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:38:24.455142+00:00
-- url     : https://prove2.me/submissions/11e68577-286a-480f-b607-7c009b6b4d94

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a91_original_uniform_gaussian_physical_stop_crossing_unique
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal

/-- The actual stop-straddling set of source cells of the original Gaussian uniform physical mesh has cardinality at most one. -/
theorem solution (n m : ℕ) (ρ : ℝ≥0) :
    ((Finset.range m).filter (fun (i : ℕ) =>
      (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ ∧
      ρ ≤ ((Nat.succ i : ℕ) : ℝ≥0) *
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1)))).card ≤ 1 := by
  classical
  apply (Finset.card_le_one).2
  intro i hi j hj
  rcases Finset.mem_filter.mp hi with ⟨_, his, hie⟩
  rcases Finset.mem_filter.mp hj with ⟨_, hjs, hje⟩
  by_cases h : i = j
  · exact h
  rcases lt_or_gt_of_ne h with hij | hji
  · exact False.elim
      (avram_ga_a91_original_uniform_gaussian_physical_stop_crossing_unique
        n m i j ρ hij his hie hjs)
  · exact False.elim
      (avram_ga_a91_original_uniform_gaussian_physical_stop_crossing_unique
        n m j i ρ hji hjs hje his)
