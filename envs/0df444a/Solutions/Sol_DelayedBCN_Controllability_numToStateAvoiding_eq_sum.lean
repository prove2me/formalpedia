-- Prove2me | solution 1 for DelayedBCN.Controllability.numToStateAvoiding_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:30:09.579253+00:00
-- url     : https://prove2.me/submissions/eba73526-c4f8-4f91-9a0f-3d9ddfcc6a35

import Mathlib
import Definitions.Def_DelayedBCN_Controllability_Model
import Definitions.Def_DelayedBCN_Controllability_Matrix
import Theorems.Thm_DelayedBCN_Controllability_card_controls_avoiding_eq_zeroed_pow

open DelayedBCN.Controllability

theorem solution {μ n m : ℕ} [NeZero μ] (F : Network μ n m)
    (Cs : Finset (State n)) (a : Traj μ n) (bs : State n) (k : ℕ) (hk : 0 < k) :
    numToStateAvoiding F k a bs Cs = ∑ b ∈ xiLast bs, numAvoiding F k a b (xiForbidden Cs) ∧
      numToStateAvoiding F k a bs Cs =
        ∑ b ∈ xiLast bs, (QZeroed F (xiForbidden Cs) ^ k) b a := by
  have hiff : ∀ X : Traj μ n, X ∉ xiForbidden Cs ↔ ∀ j : Fin μ, X j ∉ Cs := by
    intro X
    simp only [xiForbidden, Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
  have h1 : numToStateAvoiding F k a bs Cs =
      ∑ b ∈ xiLast bs, numAvoiding F k a b (xiForbidden Cs) := by
    rw [numToStateAvoiding]
    rw [Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter (fun U : Fin k → Input m =>
        currentState (trajAt F a U k) = bs ∧ ∀ i : Fin (k + 1), ∀ j : Fin μ, trajAt F a U i j ∉ Cs))
      (t := xiLast bs) (f := fun U : Fin k → Input m => trajAt F a U k)
      (fun U hU => by
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hU
        simpa only [Finset.mem_coe, xiLast, Finset.mem_filter, Finset.mem_univ, true_and] using hU.1)]
    apply Finset.sum_congr rfl
    intro b hb
    have hcb : currentState b = bs := by
      simpa only [xiLast, Finset.mem_filter, Finset.mem_univ, true_and] using hb
    rw [numAvoiding]
    congr 1
    apply Finset.ext
    intro U
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hiff]
    constructor
    · rintro ⟨⟨-, hav⟩, hUb⟩
      exact ⟨hUb, hav⟩
    · rintro ⟨hUb, hav⟩
      exact ⟨⟨by rw [hUb]; exact hcb, hav⟩, hUb⟩
  refine ⟨h1, ?_⟩
  rw [h1]
  apply Finset.sum_congr rfl
  intro b _
  exact card_controls_avoiding_eq_zeroed_pow F (xiForbidden Cs) a b k hk
