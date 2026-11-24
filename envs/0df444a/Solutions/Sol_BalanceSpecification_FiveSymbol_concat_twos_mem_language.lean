-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.concat_twos_mem_language
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:46:18.960523+00:00
-- url     : https://prove2.me/submissions/b97769ff-7e52-47fa-9584-6d4dc348a31b

module
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Theorems.Thm_BalanceSpecification_FiveSymbol_forbiddenWord_get_zero
public import Theorems.Thm_BalanceSpecification_FiveSymbol_forbiddenWord_get_last
public import Theorems.Thm_BalanceSpecification_FiveSymbol_mem_language_iff_avoids
public import Theorems.Thm_BalanceSpecification_FiveSymbol_infix_left_of_end_le
public import Theorems.Thm_BalanceSpecification_FiveSymbol_infix_right_of_start_le
public import Theorems.Thm_BalanceSpecification_FiveSymbol_getElem_infix_witness
public import Theorems.Thm_BalanceSpecification_FiveSymbol_getElem_two_bridge
public import Theorems.Thm_BalanceSpecification_FiveSymbol_forbiddenWord_left_one
public import Theorems.Thm_BalanceSpecification_FiveSymbol_forbiddenWord_right_three
public import Theorems.Thm_BalanceSpecification_FiveSymbol_forbiddenWord_right_one
public import Theorems.Thm_BalanceSpecification_FiveSymbol_shortlex_length_add_one_lt_markerLength
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_shortlexWord_zero
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.shortlexWord_zero



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol
namespace BalanceSpecification.FiveSymbol
theorem _root_.solution {u v : Word Alphabet}
    (hu : u ∈ language shift) (hv : v ∈ language shift) {L : ℕ}
    (hL : u.length < L) : u ++ List.replicate L 2 ++ v ∈ language shift := by
  apply (mem_language_iff_avoids _).mpr
  intro j hj hocc
  obtain ⟨p, q, heq⟩ := hocc
  have heq : u ++ List.replicate L 2 ++ v = p ++ forbiddenWord j ++ q := heq.symm
  have hlen := congrArg List.length heq
  simp only [List.length_append, List.length_replicate] at hlen
  have hflen := forbiddenWord_length_pos j
  have hfirst := getElem_infix_witness heq (i := 0) hflen
  simp only [Nat.add_zero, forbiddenWord_get_zero] at hfirst
  have hlast := getElem_infix_witness heq
    (i := (forbiddenWord j).length - 1) (by omega)
  simp only [forbiddenWord_get_last] at hlast
  have hstart_bound : p.length < u.length + L := by
    by_contra h
    apply ((mem_language_iff_avoids v).mp hv) j hj
    exact infix_right_of_start_le heq (by
      simp only [List.length_append, List.length_replicate]
      omega)
  have hstart : p.length < u.length := by
    by_contra h
    have htwo := getElem_two_bridge (u := u) (v := v) (L := L)
      (by omega : u.length ≤ p.length) hstart_bound
    exact (by decide : (2 : Alphabet) ≠ 0) (htwo.symm.trans hfirst)
  have hend_bound : u.length < p.length + (forbiddenWord j).length := by
    by_contra h
    apply ((mem_language_iff_avoids u).mp hu) j hj
    apply infix_left_of_end_le (p := p) (q := q)
      (v := List.replicate L 2 ++ v) _ (by omega)
    simpa only [List.append_assoc] using heq
  have hend : u.length + L < p.length + (forbiddenWord j).length := by
    by_contra h
    have htwo := getElem_two_bridge (u := u) (v := v) (L := L)
      (t := p.length + ((forbiddenWord j).length - 1)) (by omega) (by omega)
    exact (by decide : (2 : Alphabet) ≠ 4) (htwo.symm.trans hlast)
  have hleft_inside : p.length + markerLength j + 1 ≤ u.length := by
    by_contra h
    let i := u.length - (p.length + 1)
    have hi : i < markerLength j := by dsimp only [i]; omega
    have hread := getElem_infix_witness heq (i := i + 1)
      (by rw [length_forbiddenWord]; omega)
    have hone := hread.trans (forbiddenWord_left_one j hi)
    have hidx : p.length + (i + 1) = u.length := by dsimp only [i]; omega
    simp only [hidx] at hone
    have htwo := getElem_two_bridge (u := u) (v := v) (L := L) (t := u.length)
      (le_refl _) (by omega)
    exact (by decide : (2 : Alphabet) ≠ 1) (htwo.symm.trans hone)
  have hright_inside : u.length + L ≤ p.length + rightOffset j := by
    by_contra h
    by_cases hright : u.length ≤ p.length + rightOffset j
    · have hread := getElem_infix_witness heq (i := rightOffset j)
        (by rw [forbiddenWord_length_rightOffset]; omega)
      have hthree := hread.trans (forbiddenWord_right_three j)
      have htwo := getElem_two_bridge (u := u) (v := v) (L := L) hright (by omega)
      exact (by decide : (2 : Alphabet) ≠ 3) (htwo.symm.trans hthree)
    · let i := u.length - (p.length + rightOffset j + 1)
      have hfsize := forbiddenWord_length_rightOffset j
      have hi : i < markerLength j := by dsimp only [i]; omega
      have hread := getElem_infix_witness heq (i := rightOffset j + (i + 1))
        (by rw [forbiddenWord_length_rightOffset]; omega)
      have hone := hread.trans (forbiddenWord_right_one j hi)
      have hidx : p.length + (rightOffset j + (i + 1)) = u.length := by
        dsimp only [i]
        omega
      simp only [hidx] at hone
      have htwo := getElem_two_bridge (u := u) (v := v) (L := L) (t := u.length)
        (le_refl _) (by omega)
      exact (by decide : (2 : Alphabet) ≠ 1) (htwo.symm.trans hone)
  have hoff : rightOffset j = markerLength j + 2 +
      (shortlexWord (A := Alphabet) j).length := by
    simp only [rightOffset, length_markerLeft]
  have hshort := shortlex_length_add_one_lt_markerLength hj
  omega
end BalanceSpecification.FiveSymbol
