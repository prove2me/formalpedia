-- Prove2me | solution 2 for AvramDividend.Classical.avram_ga_a95_original_gaussian_uniform_mesh_true_crossing_card_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:11:52.404235+00:00
-- url     : https://prove2.me/submissions/712fa93a-6f28-4207-a3bc-89e4929aa008

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
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
  have hBad (p q : ℕ) (hpq : p < q)
      (hps : (p : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ)
      (hpe : ρ ≤ ((Nat.succ p : ℕ) : ℝ≥0) *
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1)))
      (hqs : (q : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ) :
      False := by
    have hpq' : ((Nat.succ p : ℕ) : ℝ≥0) ≤ (q : ℝ≥0) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hpq)
    have hle : ((Nat.succ p : ℕ) : ℝ≥0) *
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) ≤
        (q : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) :=
      mul_le_mul_of_nonneg_right hpq' (by positivity)
    exact (not_lt_of_ge (le_trans hpe hle)) hqs
  by_cases h : i = j
  · exact h
  rcases lt_or_gt_of_ne h with hij | hji
  · exact False.elim (hBad i j hij his hie hjs)
  · exact False.elim (hBad j i hji hjs hje his)
