-- Prove2me | solution 1 for F6SmallBlockTokenCapacity.TokenRun.three_incidence_equality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:41:47.642092+00:00
-- url     : https://prove2.me/submissions/554bcc54-2b9f-4713-8ad7-0ad53479ea90

import Mathlib
import Definitions.Def_StableMarriageF6_F6SmallBlockTokenCapacity
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_mem_participationSteps
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_participation_count
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_incidence_sum
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_incidence_bounds
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
theorem _root_.solution (P : TokenRun B W 3) (hB : Fintype.card B ≤ 3) :
    Fintype.card B = 3 ∧
    (∀ i : Fin 3, (P.support i).card = 2) ∧
    (∀ b : B, (P.participationSteps b).card = 2) := by
  classical
  have hcount (b : B) : (P.participationSteps b).card ≤ 2 := by
    have h := P.participation_count b
    omega
  have hlo : 6 ≤ ∑ i : Fin 3, (P.support i).card := P.incidence_bounds.1
  have hhi : (∑ i : Fin 3, (P.support i).card) ≤ Fintype.card B * 2 := by
    rw [P.incidence_sum]
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset B)) (fun b _ => hcount b)
    simpa [participationSteps] using h
  have hcard : Fintype.card B = 3 := by omega
  have htotal : (∑ i : Fin 3, (P.support i).card) = 6 := by omega
  refine ⟨hcard, ?_, ?_⟩
  · have heq : (∑ _i : Fin 3, (2 : ℕ)) = ∑ i : Fin 3, (P.support i).card := by
      simpa using htotal.symm
    have h := (Finset.sum_eq_sum_iff_of_le (fun i _ => P.HMIN i)).mp heq
    exact fun i => (h i (Finset.mem_univ i)).symm
  · have heq : (∑ b : B, (P.participationSteps b).card) = ∑ _b : B, (2 : ℕ) := by
      simpa [participationSteps, hcard, P.incidence_sum] using htotal
    have h := (Finset.sum_eq_sum_iff_of_le (fun b _ => hcount b)).mp heq
    exact fun b => h b (Finset.mem_univ b)
end F6SmallBlockTokenCapacity.TokenRun
