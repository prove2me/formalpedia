-- Prove2me | solution 1 for F6SmallBlockTokenCapacity.TokenRun.participation_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:25:34.388082+00:00
-- url     : https://prove2.me/submissions/3171a51f-1f68-434e-b85c-c7334cb3d017

import Mathlib
import Definitions.Def_StableMarriageF6_F6SmallBlockTokenCapacity
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_mem_participationSteps
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_rank_after_lt
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_initial_rank_lt_after
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
theorem _root_.solution (b : B) :
    (R.participationSteps b).card ≤ Fintype.card B - 1 := by
  classical
  have hinj : Set.InjOn (fun i : Fin q => R.state i.succ b)
      (R.participationSteps b : Set (Fin q)) := by
    intro i hi j hj heq
    change R.state i.succ b = R.state j.succ b at heq
    have hi' : b ∈ R.support i := (R.mem_participationSteps b i).mp hi
    have hj' : b ∈ R.support j := (R.mem_participationSteps b j).mp hj
    rcases lt_trichotomy i j with hij | hij | hij
    · have h := R.rank_after_lt b hij hj'
      rw [heq] at h
      exact (lt_irrefl _ h).elim
    · exact hij
    · have h := R.rank_after_lt b hij hi'
      rw [heq] at h
      exact (lt_irrefl _ h).elim
  have hmap : Set.MapsTo (fun i : Fin q => R.state i.succ b)
      (R.participationSteps b : Set (Fin q))
      ((Finset.univ.erase (R.state 0 b) : Finset W) : Set W) := by
    intro i hi
    have h := R.initial_rank_lt_after b ((R.mem_participationSteps b i).mp hi)
    have hne : R.state i.succ b ≠ R.state 0 b := by
      intro heq
      rw [heq] at h
      exact lt_irrefl _ h
    simpa using hne
  have hc := Finset.card_le_card_of_injOn (fun i : Fin q => R.state i.succ b) hmap hinj
  have hBW : Fintype.card B = Fintype.card W := Fintype.card_congr (R.state 0)
  simpa [Finset.card_erase_of_mem, hBW] using hc
end F6SmallBlockTokenCapacity.TokenRun
