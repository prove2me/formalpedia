-- Prove2me | solution 1 for CompOT.Assignment.perm_feasible
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-09T17:00:53.382826+00:00
-- url     : https://prove2.me/submissions/483622cf-412f-4880-bd51-1932408180c3

import Mathlib
import Definitions.Def_CompOT_Assignment_Defs

open CompOT.Assignment

theorem solution {n : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (Fin n)) :
    permCoupling σ ∈ couplings (uniform n) (uniform n) := by
  refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
  · unfold permCoupling
    split_ifs <;> positivity
  · simp [permCoupling, uniform]
  · simp only [permCoupling, uniform]
    rw [Finset.sum_eq_single (σ.symm j)]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (by rw [h]; simp)
    · simp
