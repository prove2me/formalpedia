-- Prove2me | solution 1 for F6SmallBlockTokenCapacity.TokenRun.incidence_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:34:53.670052+00:00
-- url     : https://prove2.me/submissions/e392d206-3ba1-485f-9da3-2ff21fe825e1

import Mathlib
import Definitions.Def_StableMarriageF6_F6SmallBlockTokenCapacity
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_mem_participationSteps
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_participation_count
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_incidence_sum
attribute [local simp] F6SmallBlockTokenCapacity.TokenRun.mem_participationSteps

set_option autoImplicit true
open scoped BigOperators
open Classical
noncomputable section
open F6SmallBlockTokenCapacity
variable {B W : Type*} [Fintype B] [Fintype W] {q : ℕ}
open F6SmallBlockTokenCapacity.TokenRun
variable (R : TokenRun B W q)
namespace F6SmallBlockTokenCapacity.TokenRun
theorem _root_.solution :
    2 * q ≤ (∑ i : Fin q, (R.support i).card) ∧
    (∑ i : Fin q, (R.support i).card) ≤ Fintype.card B * (Fintype.card B - 1) := by
  classical
  constructor
  · have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin q)))
      (fun i _ => R.HMIN i)
    simpa [Nat.mul_comm] using h
  · rw [R.incidence_sum]
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset B))
      (fun b _ => R.participation_count b)
    simpa [participationSteps] using h
end F6SmallBlockTokenCapacity.TokenRun
