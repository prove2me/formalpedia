-- Prove2me | solution 1 for ConjCoord.Proof.reps112_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:52:55.678805+00:00
-- url     : https://prove2.me/submissions/603bf716-1c15-4b67-b23e-f460181fcf63

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Reps
public import Theorems.Thm_ConjCoord_Proof_reps_eq_card_sol
public import Theorems.Thm_ConjCoord_Proof_mem_sol
public import Theorems.Thm_ConjCoord_Proof_sq_mod4
public import Theorems.Thm_ConjCoord_Proof_card_eq_two_mul_filter

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
variable {n : ℕ}
namespace ConjCoord.Proof
theorem _root_.solution (hn : n % 2 = 1) : reps 1 1 2 n = 2 * reps 1 2 4 n := by
  rw [reps_eq_card_sol, reps_eq_card_sol]
  set S := sol 1 1 2 n
  have hS : ∀ v ∈ S, v.1 ^ 2 + v.2.1 ^ 2 + 2 * v.2.2 ^ 2 = n := by
    intro v hv; have := (mem_sol one_pos one_pos two_pos v).mp hv; push_cast at this; linarith
  have par : ∀ v ∈ S, (Even v.1 ↔ ¬ Even v.2.1) := by
    intro v hv
    have := hS v hv
    rw [Int.not_even_iff_odd]
    rcases sq_mod4 v.1 with ⟨hX, hX'⟩ | ⟨hX, hX'⟩ <;>
    rcases sq_mod4 v.2.1 with ⟨hU, hU'⟩ | ⟨hU, hU'⟩
    · exfalso; omega
    · exact ⟨fun _ => hU, fun _ => hX⟩
    · exact ⟨fun h => absurd h (Int.not_even_iff_odd.mpr hX), fun h => absurd hU (Int.not_even_iff_odd.mpr h)⟩
    · exfalso; omega
  rw [card_eq_two_mul_filter S (fun v => (v.2.1, v.1, v.2.2)) (fun v => Even v.2.1) ?_ ?_ ?_]
  · congr 1
    refine card_nbij' (fun v => (v.1, v.2.2, v.2.1 / 2)) (fun v => (v.1, 2 * v.2.2, v.2.1)) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [mem_coe, mem_filter] at hv
      rw [mem_coe, mem_sol one_pos two_pos (by norm_num)]
      obtain ⟨r, hr⟩ := hv.2
      have e : v.2.1 / 2 = r := by omega
      dsimp only; rw [e]; have := hS v hv.1; rw [hr] at this; push_cast; linarith
    · intro v hv
      rw [mem_coe, mem_sol one_pos two_pos (by norm_num)] at hv
      simp only [mem_coe, mem_filter, S]
      refine ⟨?_, even_two_mul _⟩
      rw [mem_sol one_pos one_pos two_pos]; push_cast at hv ⊢; linarith
    · intro v hv
      simp only [mem_coe, mem_filter] at hv
      obtain ⟨r, hr⟩ := hv.2
      ext <;> simp; omega
    · intro v _
      ext <;> simp
  · intro v hv
    have := hS v hv
    rw [mem_sol one_pos one_pos two_pos]; push_cast; linarith
  · intro v _; rfl
  · intro v hv
    exact par v hv
end ConjCoord.Proof
