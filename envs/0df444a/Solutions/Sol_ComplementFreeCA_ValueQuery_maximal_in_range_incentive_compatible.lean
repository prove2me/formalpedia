-- Prove2me | solution 1 for ComplementFreeCA.ValueQuery.maximal_in_range_incentive_compatible
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:44:28.462322+00:00
-- url     : https://prove2.me/submissions/137bf31e-c691-4e25-a8c0-1b5d547d27f2

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Tactic
import Definitions.Def_ComplementFreeCA_ValueQuery_Basic
open Finset ComplementFreeCA.ValueQuery

theorem solution {n m : ℕ}
    (D : (Finset (Fin m) → ℝ) → Prop) (R : Set (Fin n → Finset (Fin m)))
    (f : (Fin n → Finset (Fin m) → ℝ) → Fin n → Finset (Fin m))
    (hf : IsMaximalInRange D R f) : IncentiveCompatibleOn D f := by
  classical
  intro v hv i v' hv'
  have hu : ∀ k, D (Function.update v i v' k) := by
    intro k
    by_cases hki : k = i
    · subst k
      simpa using hv'
    · simpa [Function.update_of_ne hki] using hv k
  have h := (hf v hv).2 _ (hf _ hu).1
  have heq : ∀ A : Fin n → Finset (Fin m),
      v i (A i) + ∑ k ∈ univ.erase i, Function.update v i v' k (A k) = welfare v A := by
    intro A
    rw [welfare, ← add_sum_erase univ (fun k => v k (A k)) (mem_univ i)]
    congr 1
    apply sum_congr rfl
    intro k hk
    rw [Function.update_of_ne (mem_erase.mp hk).1]
  unfold vcgUtility vcgPayment
  rw [heq]
  unfold welfare at h ⊢
  rw [← add_sum_erase univ (fun k => v k (f v k)) (mem_univ i)] at h
  exact h
