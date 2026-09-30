-- Prove2me | solution 1 for ComplementFreeCA.CFRounding.opt_le_lpValue
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:42:32.23529+00:00
-- url     : https://prove2.me/submissions/b4c74ff0-d952-4898-85f7-f5614457f08c

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Tactic
import Definitions.Def_ComplementFreeCA_CFRounding_Auction
import Definitions.Def_ComplementFreeCA_CFRounding_LP
open Finset ComplementFreeCA.CFRounding

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (x : Fin n → Finset (Fin m) → ℝ) (hx : IsOptimalLP v x)
    (O : Fin n → Finset (Fin m)) (hO : IsAllocation O) :
    welfare v O ≤ lpValue v x := by
  classical
  let y : Fin n → Finset (Fin m) → ℝ := fun i S => if S = O i then 1 else 0
  have hy : IsLPFeasible y := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      simp only [y, sum_ite_eq', mem_filter, mem_univ, true_and]
      by_cases he : ∃ i, j ∈ O i
      · obtain ⟨i, hi⟩ := he
        have hother : ∀ i' ≠ i, j ∉ O i' := by
          intro i' hne hj
          exact disjoint_left.mp (hO i' i hne) hj hi
        rw [sum_eq_single i]
        · simp [hi]
        · intro i' hi' hne
          simp [hother i' hne]
        · simp
      · simp only [not_exists] at he
        simp [he]
    · intro i
      simp [y]
    · intro i S
      simp only [y]
      split_ifs <;> norm_num
  have heq : lpValue v y = welfare v O := by
    simp [lpValue, welfare, y, ite_mul]
  rw [← heq]
  exact hx.2 y hy
