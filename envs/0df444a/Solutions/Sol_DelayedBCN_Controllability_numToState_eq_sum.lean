-- Prove2me | solution 1 for DelayedBCN.Controllability.numToState_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:26:33.174153+00:00
-- url     : https://prove2.me/submissions/1b3533f1-aa00-4cd7-bb24-cf02030d701d

import Mathlib
import Definitions.Def_DelayedBCN_Controllability_Model
import Definitions.Def_DelayedBCN_Controllability_Matrix
import Theorems.Thm_DelayedBCN_Controllability_card_controls_eq_pow

open DelayedBCN.Controllability

theorem solution {μ n m : ℕ} [NeZero μ] (F : Network μ n m)
    (a : Traj μ n) (bs : State n) (k : ℕ) (hk : 0 < k) :
    numToState F k a bs = ∑ b ∈ xiLast bs, numSteering F k a b ∧
      numToState F k a bs = ∑ b ∈ xiLast bs, (Q F ^ k) b a := by
  have h1 : numToState F k a bs = ∑ b ∈ xiLast bs, numSteering F k a b := by
    rw [numToState]
    rw [Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter (fun U : Fin k → Input m => currentState (trajAt F a U k) = bs))
      (t := xiLast bs) (f := fun U : Fin k → Input m => trajAt F a U k)
      (fun U hU => by
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hU
        simpa only [Finset.mem_coe, xiLast, Finset.mem_filter, Finset.mem_univ, true_and] using hU)]
    apply Finset.sum_congr rfl
    intro b hb
    have hcb : currentState b = bs := by
      simpa only [xiLast, Finset.mem_filter, Finset.mem_univ, true_and] using hb
    rw [numSteering]
    congr 1
    apply Finset.ext
    intro U
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, hUb⟩
      exact hUb
    · intro hUb
      exact ⟨by rw [hUb]; exact hcb, hUb⟩
  refine ⟨h1, ?_⟩
  rw [h1]
  apply Finset.sum_congr rfl
  intro b _
  exact card_controls_eq_pow F a b k
