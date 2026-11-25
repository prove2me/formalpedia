-- Prove2me | solution 1 for ConjCoord.Proof.r3_eq_three_mul_reps122
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:52:47.666543+00:00
-- url     : https://prove2.me/submissions/7ab217a2-659c-4aa4-b05a-19f3bfa6e348

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Reps
public import Theorems.Thm_ConjCoord_Proof_reps_eq_card_sol
public import Theorems.Thm_ConjCoord_Proof_mem_sol
public import Theorems.Thm_ConjCoord_Proof_sq_mod4
public import Theorems.Thm_ConjCoord_Proof_card_eq_three
public import Theorems.Thm_ConjCoord_Proof_mem_sol111
public import Theorems.Thm_ConjCoord_Proof_one_odd

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
variable {n : ℕ}
namespace ConjCoord.Proof
theorem _root_.solution (hn : n % 4 = 1) : r3 n = 3 * reps 1 2 2 n := by
  unfold r3
  rw [reps_eq_card_sol, reps_eq_card_sol]
  set S := sol 1 1 1 n
  have hS : ∀ v ∈ S, v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = n := fun v hv => (mem_sol111 v).mp hv
  rw [card_eq_three S (fun v => Odd v.1) (fun v => Odd v.2.1) (fun v => Odd v.2.2)
    (fun v hv => one_odd hn (hS v hv))]
  have e2 : (S.filter fun v => Odd v.2.1).card = (S.filter fun v => Odd v.1).card := by
    refine card_nbij' (fun v => (v.2.1, v.1, v.2.2)) (fun v => (v.2.1, v.1, v.2.2)) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv ⊢
      exact ⟨by linarith [hv.1], hv.2⟩
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv ⊢
      exact ⟨by linarith [hv.1], hv.2⟩
    · intro v _; rfl
    · intro v _; rfl
  have e3 : (S.filter fun v => Odd v.2.2).card = (S.filter fun v => Odd v.1).card := by
    refine card_nbij' (fun v => (v.2.2, v.2.1, v.1)) (fun v => (v.2.2, v.2.1, v.1)) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv ⊢
      exact ⟨by linarith [hv.1], hv.2⟩
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv ⊢
      exact ⟨by linarith [hv.1], hv.2⟩
    · intro v _; rfl
    · intro v _; rfl
  have e1 : (S.filter fun v => Odd v.1).card = (sol 1 2 2 n).card := by
    symm
    refine card_nbij' (fun v => (v.1, v.2.1 + v.2.2, v.2.1 - v.2.2))
      (fun v => (v.1, (v.2.1 + v.2.2) / 2, (v.2.1 - v.2.2) / 2)) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv ⊢
      rw [mem_sol one_pos two_pos two_pos] at hv
      push_cast at hv
      refine ⟨by linarith, ?_⟩
      rcases sq_mod4 v.1 with ⟨_, h1⟩ | ⟨h1, _⟩
      · exfalso; omega
      · exact h1
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv
      rw [mem_coe, mem_sol one_pos two_pos two_pos]
      push_cast
      rcases one_odd hn hv.1 with ⟨-, hU, hV⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩
      · rw [Int.not_odd_iff_even] at hU hV
        obtain ⟨u, hu⟩ := hU; obtain ⟨w, hw⟩ := hV
        have e1 : (v.2.1 + v.2.2) / 2 = u + w := by omega
        have e2 : (v.2.1 - v.2.2) / 2 = u - w := by omega
        rw [e1, e2]; rw [hu, hw] at hv; linarith [hv.1]
      · exact absurd hv.2 h
      · exact absurd hv.2 h
    · intro v _
      ext <;> simp <;> omega
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv
      rcases one_odd hn hv.1 with ⟨-, hU, hV⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩
      · rw [Int.not_odd_iff_even] at hU hV
        obtain ⟨u, hu⟩ := hU; obtain ⟨w, hw⟩ := hV
        ext <;> simp <;> omega
      · exact absurd hv.2 h
      · exact absurd hv.2 h
  omega
end ConjCoord.Proof
