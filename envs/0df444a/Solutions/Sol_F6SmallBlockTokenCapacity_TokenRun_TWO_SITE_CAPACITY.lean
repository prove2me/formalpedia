-- Prove2me | solution 1 for F6SmallBlockTokenCapacity.TokenRun.TWO_SITE_CAPACITY
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:35:22.595236+00:00
-- url     : https://prove2.me/submissions/e9cc900b-d151-4704-9ae2-9eef46192796

import Mathlib
import Definitions.Def_StableMarriageF6_F6SmallBlockTokenCapacity
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_mem_participationSteps
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_participation_count
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
theorem _root_.solution (R : TokenRun B W q) (hB : Fintype.card B ≤ 2) : q ≤ 1 := by
  classical
  by_contra hq
  have htwo : 2 ≤ q := by omega
  let P := R.firstSteps 2 htwo
  have hfull (i : Fin 2) : P.support i = Finset.univ := by
    apply Finset.eq_univ_of_card
    have hlo := P.HMIN i
    have hhi := (P.support i).card_le_univ
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < 2) (P.HMIN 0))
  have hc := P.participation_count b
  have heq : (P.participationSteps b).card = 2 := by
    simp [participationSteps, hfull]
  omega
end F6SmallBlockTokenCapacity.TokenRun
