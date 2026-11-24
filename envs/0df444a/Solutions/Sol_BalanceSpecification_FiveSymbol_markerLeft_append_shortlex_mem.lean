-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.markerLeft_append_shortlex_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:46:20.265008+00:00
-- url     : https://prove2.me/submissions/7b54677e-9da3-43f6-bb67-deb691e96e20

module
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Theorems.Thm_BalanceSpecification_FiveSymbol_forbiddenWord_get_zero
public import Theorems.Thm_BalanceSpecification_FiveSymbol_mem_language_iff_avoids
public import Theorems.Thm_BalanceSpecification_FiveSymbol_infix_right_of_start_le
public import Theorems.Thm_BalanceSpecification_FiveSymbol_getElem_infix_witness
public import Theorems.Thm_BalanceSpecification_FiveSymbol_forbiddenWord_left_one
public import Theorems.Thm_BalanceSpecification_FiveSymbol_markerLeft_one
public import Theorems.Thm_BalanceSpecification_FiveSymbol_markerLeft_two
public import Theorems.Thm_BalanceSpecification_FiveSymbol_forbiddenWord_left_two
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
theorem _root_.solution {j : ℕ} (_hj : 1 ≤ j)
    (hw : shortlexWord (A := Alphabet) j ∈ language shift) :
    markerLeft j ++ shortlexWord j ∈ language shift := by
  apply (mem_language_iff_avoids _).mpr
  intro k hk hocc
  obtain ⟨p, q, heq⟩ := hocc
  have heq : markerLeft j ++ shortlexWord j = p ++ forbiddenWord k ++ q := heq.symm
  have hlen := congrArg List.length heq
  simp only [List.length_append] at hlen
  have hflen := forbiddenWord_length_pos k
  have hstart : p.length < (markerLeft j).length := by
    by_contra h
    exact ((mem_language_iff_avoids _).mp hw) k hk
      (infix_right_of_start_le heq (by omega))
  have hread := getElem_infix_witness heq (i := 0) hflen
  simp only [Nat.add_zero, forbiddenWord_get_zero] at hread
  have hmark : (markerLeft j)[p.length]'hstart = 0 := by
    simpa only [List.getElem_append_left hstart] using hread
  have hpzero : p.length = 0 := by
    by_contra h
    by_cases hone : p.length < markerLength j + 1
    · have hi : p.length - 1 < markerLength j := by omega
      have hidx : p.length - 1 + 1 = p.length := by omega
      have hx := markerLeft_one j hi
      simp only [hidx] at hx
      exact (by decide : (1 : Alphabet) ≠ 0) (hx.symm.trans hmark)
    · have hidx : p.length = markerLength j + 1 := by rw [length_markerLeft] at hstart; omega
      simp only [hidx, markerLeft_two] at hmark
      exact (by decide : (2 : Alphabet) ≠ 0) hmark
  have hr : markerLength k = markerLength j := by
    apply le_antisymm
    · by_contra h
      have hread := getElem_infix_witness heq (i := markerLength j + 1)
        (by rw [length_forbiddenWord]; omega)
      have hone := forbiddenWord_left_one k (i := markerLength j) (by omega)
      have hidx : markerLength j + 1 < (markerLeft j).length := by rw [length_markerLeft]; omega
      simp only [hpzero, Nat.zero_add, List.getElem_append_left hidx, markerLeft_two] at hread
      exact (by decide : (2 : Alphabet) ≠ 1) (hread.trans hone)
    · by_contra h
      have hread := getElem_infix_witness heq (i := markerLength k + 1)
        (by rw [length_forbiddenWord]; omega)
      have hone := markerLeft_one j (i := markerLength k) (by omega)
      have hidx : markerLength k + 1 < (markerLeft j).length := by rw [length_markerLeft]; omega
      simp only [hpzero, Nat.zero_add, List.getElem_append_left hidx,
        forbiddenWord_left_two] at hread
      exact (by decide : (1 : Alphabet) ≠ 2) (hone.symm.trans hread)
  have hkj : k = j := Nat.pow_right_injective (by decide : 2 ≤ 5) hr
  subst k
  have hsize := length_forbiddenWord j
  have hmarker := length_markerLeft j
  omega
end BalanceSpecification.FiveSymbol
