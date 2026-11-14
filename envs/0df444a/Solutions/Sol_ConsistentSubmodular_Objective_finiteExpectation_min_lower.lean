-- Prove2me | solution 1 for ConsistentSubmodular.Objective.finiteExpectation_min_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:37:07.524773+00:00
-- url     : https://prove2.me/submissions/6b3df5ee-e1cd-40d4-8d1b-9edd29764d2b

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_FiniteExpectation
import Theorems.Thm_ConsistentSubmodular_Objective_finiteExpectation_lipschitz

section

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem solution (V : ℝ) (hV0 : 0 ≤ V)
    (hV : ∀ i, f.value {i} - f.value ∅ ≤ V)
    (p q : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) :
    finiteExpectation p f.value - V * ∑ i, |p i - q i| ≤
      finiteExpectation (fun i => min (p i) (q i)) f.value := by
  have hmin i : 0 ≤ min (p i) (q i) ∧ min (p i) (q i) ≤ 1 :=
    ⟨le_min (hp i).1 (hq i).1, (min_le_left _ _).trans (hp i).2⟩
  have hdist : (∑ i, |p i - min (p i) (q i)|) ≤ ∑ i, |p i - q i| := by
    apply Finset.sum_le_sum
    intro i _
    by_cases h : p i ≤ q i
    · rw [min_eq_left h, sub_self, abs_zero]
      exact abs_nonneg _
    · rw [min_eq_right (le_of_not_ge h)]
  have h := f.finiteExpectation_lipschitz V hV0 hV p _ hp hmin
  have hab := (le_abs_self (finiteExpectation p f.value -
    finiteExpectation (fun i => min (p i) (q i)) f.value)).trans h
  have := mul_le_mul_of_nonneg_left hdist hV0
  linarith

end
