-- Prove2me | solution 1 for CompOT.Assignment.assignment_cost
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-09T17:00:52.76927+00:00
-- url     : https://prove2.me/submissions/d8d6c05b-2fc8-4e83-a8f1-257d787db716

import Mathlib
import Definitions.Def_CompOT_Assignment_Defs

open CompOT.Assignment

theorem solution {n : ℕ} (hn : 0 < n)
    (C : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n)) :
    frob C (permCoupling σ) = assignmentCost C σ := by
  simp only [frob, permCoupling, assignmentCost, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
