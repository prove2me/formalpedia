-- Prove2me | solution 1 for ConjCoord.Proof.r3_two_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:52:49.653824+00:00
-- url     : https://prove2.me/submissions/5c6f1cf5-47da-45e7-8815-e9d5686d6593

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Reps
public import Theorems.Thm_ConjCoord_Proof_reps_eq_card_sol
public import Theorems.Thm_ConjCoord_Proof_mem_sol
public import Theorems.Thm_ConjCoord_Proof_card_eq_three
public import Theorems.Thm_ConjCoord_Proof_mem_sol111
public import Theorems.Thm_ConjCoord_Proof_one_even

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
variable {n : ℕ}
namespace ConjCoord.Proof
theorem _root_.solution (hn : n % 2 = 1) : r3 (2 * n) = 3 * reps 1 1 2 n := by
  unfold r3
  rw [reps_eq_card_sol, reps_eq_card_sol]
  set S := sol 1 1 1 (2 * n)
  have hS : ∀ v ∈ S, v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = 2 * n := by
    intro v hv; have := (mem_sol111 v).mp hv; push_cast at this; exact this
  rw [card_eq_three S (fun v => Even v.1) (fun v => Even v.2.1) (fun v => Even v.2.2)
    (fun v hv => one_even hn (hS v hv))]
  have e1 : (S.filter fun v => Even v.1).card = (S.filter fun v => Even v.2.2).card := by
    refine card_nbij' (fun v => (v.2.2, v.2.1, v.1)) (fun v => (v.2.2, v.2.1, v.1)) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv ⊢
      exact ⟨by linarith [hv.1], hv.2⟩
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv ⊢
      exact ⟨by linarith [hv.1], hv.2⟩
    · intro v _; rfl
    · intro v _; rfl
  have e2 : (S.filter fun v => Even v.2.1).card = (S.filter fun v => Even v.2.2).card := by
    refine card_nbij' (fun v => (v.1, v.2.2, v.2.1)) (fun v => (v.1, v.2.2, v.2.1)) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv ⊢
      exact ⟨by linarith [hv.1], hv.2⟩
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv ⊢
      exact ⟨by linarith [hv.1], hv.2⟩
    · intro v _; rfl
    · intro v _; rfl
  have e3 : (S.filter fun v => Even v.2.2).card = (sol 1 1 2 n).card := by
    symm
    refine card_nbij' (fun v => (v.1 + v.2.1, v.1 - v.2.1, 2 * v.2.2))
      (fun v => ((v.1 + v.2.1) / 2, (v.1 - v.2.1) / 2, v.2.2 / 2)) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv ⊢
      rw [mem_sol one_pos one_pos two_pos] at hv
      push_cast at hv ⊢
      exact ⟨by linarith, even_two_mul _⟩
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv
      rw [mem_coe, mem_sol one_pos one_pos two_pos]
      push_cast at hv ⊢
      rcases one_even hn hv.1 with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨hX, hU, hV⟩
      · exact absurd hv.2 h
      · exact absurd hv.2 h
      · rw [Int.not_even_iff_odd] at hX hU
        obtain ⟨s, hs⟩ := hX; obtain ⟨t, ht⟩ := hU; obtain ⟨r, hr⟩ := hV
        have e1 : (v.1 + v.2.1) / 2 = s + t + 1 := by omega
        have e2 : (v.1 - v.2.1) / 2 = s - t := by omega
        have e3 : v.2.2 / 2 = r := by omega
        rw [e1, e2, e3]
        have h := hv.1
        rw [hs, ht, hr] at h
        ring_nf at h ⊢
        linarith
    · intro v _
      ext <;> simp <;> omega
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv
      push_cast at hv
      rcases one_even hn hv.1 with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨hX, hU, hV⟩
      · exact absurd hv.2 h
      · exact absurd hv.2 h
      · rw [Int.not_even_iff_odd] at hX hU
        obtain ⟨s, hs⟩ := hX; obtain ⟨t, ht⟩ := hU; obtain ⟨r, hr⟩ := hV
        ext <;> simp <;> omega
  omega
end ConjCoord.Proof
