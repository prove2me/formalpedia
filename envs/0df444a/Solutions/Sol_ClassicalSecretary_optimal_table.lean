-- Prove2me | solution 1 for ClassicalSecretary.optimal_table
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T16:00:04.849+00:00
-- url     : https://prove2.me/submissions/10142de6-ef55-46ae-ac09-98a89eec33cc

import Mathlib
import Definitions.Def_ClassicalSecretary_Model
import Theorems.Thm_ClassicalSecretary_successProb_cutoffRule_one
import Theorems.Thm_ClassicalSecretary_successProb_cutoffRule
import Theorems.Thm_ClassicalSecretary_exists_optimal_cutoffRule

set_option autoImplicit false

open Finset Filter Topology

namespace ClassicalSecretary.OptTable

open ClassicalSecretary

/-- Every success probability is at most `1`. -/
theorem successProb_le_one (n : ℕ) (s : StoppingRule) : successProb n s ≤ 1 := by
  unfold successProb
  apply div_le_one_of_le₀
  · rw [← Finset.card_univ]
    exact_mod_cast Finset.card_filter_le _ _
  · positivity

theorem bddAbove_successProb (n : ℕ) :
    BddAbove (Set.range fun s : StoppingRule => successProb n s) :=
  ⟨1, by rintro _ ⟨s, rfl⟩; exact successProb_le_one n s⟩

theorem successProb_le_optimalProb (n : ℕ) (s : StoppingRule) :
    successProb n s ≤ optimalProb n :=
  le_ciSup (bddAbove_successProb n) s

/-- The closed form of the success probability of the cutoff rule with cutoff `r`. -/
noncomputable def val (n r : ℕ) : ℝ :=
  if r = 1 then 1 / (n : ℝ) else ((r : ℝ) - 1) / (n : ℝ) * ∑ i ∈ Icc r n, 1 / ((i : ℝ) - 1)

theorem successProb_eq_val (n r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ n) :
    successProb n (cutoffRule r) = val n r := by
  unfold val
  split_ifs with h
  · subst h
    exact successProb_cutoffRule_one n h2
  · exact successProb_cutoffRule n r (by omega) h2

/-- If the cutoff `rs` maximizes the closed form among all cutoffs in `[1, n]`, then the
corresponding cutoff rule is optimal, and the optimal value is its value. -/
theorem key (n rs : ℕ) (hn : 1 ≤ n) (v : ℝ) (h1 : 1 ≤ rs) (h2 : rs ≤ n) (hv : val n rs = v)
    (hle : ∀ r, 1 ≤ r → r ≤ n → val n r ≤ v) :
    successProb n (cutoffRule rs) = optimalProb n ∧ optimalProb n = v := by
  obtain ⟨r0, hr1, hr2, hr3⟩ := exists_optimal_cutoffRule n hn
  have hs : successProb n (cutoffRule rs) = v := by rw [successProb_eq_val n rs h1 h2, hv]
  have hle' : optimalProb n ≤ v := by
    rw [← hr3, successProb_eq_val n r0 hr1 hr2]
    exact hle r0 hr1 hr2
  have hge : v ≤ optimalProb n := by
    rw [← hs]
    exact successProb_le_optimalProb n _
  refine ⟨?_, le_antisymm hle' hge⟩
  rw [hs]
  exact le_antisymm hge hle'

end ClassicalSecretary.OptTable

open ClassicalSecretary in
theorem solution :
    (successProb 1 (cutoffRule 1) = optimalProb 1 ∧ optimalProb 1 = 1) ∧
    (successProb 2 (cutoffRule 1) = optimalProb 2 ∧ optimalProb 2 = 1 / 2) ∧
    (successProb 3 (cutoffRule 2) = optimalProb 3 ∧ optimalProb 3 = 1 / 2) ∧
    (successProb 4 (cutoffRule 2) = optimalProb 4 ∧ optimalProb 4 = 11 / 24) ∧
    (successProb 5 (cutoffRule 3) = optimalProb 5 ∧ optimalProb 5 = 13 / 30) ∧
    (successProb 6 (cutoffRule 3) = optimalProb 6 ∧ optimalProb 6 = 77 / 180) ∧
    (successProb 7 (cutoffRule 3) = optimalProb 7 ∧ optimalProb 7 = 29 / 70) ∧
    (successProb 8 (cutoffRule 4) = optimalProb 8 ∧ optimalProb 8 = 459 / 1120) ∧
    (successProb 9 (cutoffRule 4) = optimalProb 9 ∧ optimalProb 9 = 341 / 840) ∧
    (successProb 10 (cutoffRule 4) = optimalProb 10 ∧ optimalProb 10 = 3349 / 8400) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    refine OptTable.key _ _ (by norm_num) _ (by norm_num) (by norm_num)
      (by norm_num [OptTable.val, Finset.sum_Icc_succ_top]) ?_
    intro r h1 h2
    interval_cases r <;> norm_num [OptTable.val, Finset.sum_Icc_succ_top]
