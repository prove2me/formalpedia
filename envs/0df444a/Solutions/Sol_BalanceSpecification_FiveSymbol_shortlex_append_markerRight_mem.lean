-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.shortlex_append_markerRight_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:46:29.597924+00:00
-- url     : https://prove2.me/submissions/6a0ca604-58d3-4354-a7c2-85f8ee6c749b

module
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Theorems.Thm_BalanceSpecification_FiveSymbol_forbiddenWord_get_last
public import Theorems.Thm_BalanceSpecification_FiveSymbol_mem_language_iff_avoids
public import Theorems.Thm_BalanceSpecification_FiveSymbol_infix_left_of_end_le
public import Theorems.Thm_BalanceSpecification_FiveSymbol_getElem_infix_witness
public import Theorems.Thm_BalanceSpecification_FiveSymbol_forbiddenWord_right_three
public import Theorems.Thm_BalanceSpecification_FiveSymbol_forbiddenWord_right_one
public import Theorems.Thm_BalanceSpecification_FiveSymbol_markerRight_three
public import Theorems.Thm_BalanceSpecification_FiveSymbol_markerRight_one
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
    shortlexWord j ++ markerRight j ∈ language shift := by
  apply (mem_language_iff_avoids _).mpr
  intro k hk hocc
  obtain ⟨p, q, heq⟩ := hocc
  have heq : shortlexWord j ++ markerRight j = p ++ forbiddenWord k ++ q := heq.symm
  have hlen := congrArg List.length heq
  simp only [List.length_append] at hlen
  have hflen := forbiddenWord_length_pos k
  have hrightlen := length_markerRight j
  have hend : (shortlexWord (A := Alphabet) j).length < p.length + (forbiddenWord k).length := by
    by_contra h
    exact ((mem_language_iff_avoids _).mp hw) k hk (infix_left_of_end_le heq (by omega))
  have hlast := getElem_infix_witness heq (i := (forbiddenWord k).length - 1) (by omega)
  simp only [forbiddenWord_get_last] at hlast
  let i := p.length + ((forbiddenWord k).length - 1) - (shortlexWord (A := Alphabet) j).length
  have hi : i < (markerRight j).length := by dsimp only [i]; omega
  have hmark : (markerRight j)[i]'hi = 4 := by
    have hget : (shortlexWord j ++ markerRight j)[(shortlexWord (A := Alphabet) j).length + i]'(by
        simp only [List.length_append]; omega) = (markerRight j)[i] := by
      simp only [List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    have hidx : (shortlexWord (A := Alphabet) j).length + i =
        p.length + ((forbiddenWord k).length - 1) := by dsimp only [i]; omega
    exact hget.symm.trans (by simpa only [hidx] using hlast)
  have hindex : i = markerLength j + 1 := by
    by_cases hi0 : i = 0
    · simp only [hi0, markerRight_three] at hmark
      exact False.elim ((by decide : (3 : Alphabet) ≠ 4) hmark)
    by_cases hione : i < markerLength j + 1
    · have hsmall : i - 1 < markerLength j := by omega
      have hget := markerRight_one j hsmall
      have hidx : i - 1 + 1 = i := by omega
      simp only [hidx] at hget
      exact False.elim ((by decide : (1 : Alphabet) ≠ 4) (hget.symm.trans hmark))
    · omega
  have hend_eq : p.length + (forbiddenWord k).length =
      (shortlexWord (A := Alphabet) j).length + (markerRight j).length := by
    dsimp only [i] at hindex
    omega
  have hfsize := forbiddenWord_length_rightOffset k
  have hr : markerLength k = markerLength j := by
    apply le_antisymm
    · by_contra h
      let t := (shortlexWord (A := Alphabet) j).length - (p.length + rightOffset k + 1)
      have ht : t < markerLength k := by dsimp only [t]; omega
      have hread := getElem_infix_witness heq (i := rightOffset k + (t + 1))
        (by rw [forbiddenWord_length_rightOffset]; omega)
      have hone := hread.trans (forbiddenWord_right_one k ht)
      have hidx : p.length + (rightOffset k + (t + 1)) =
          (shortlexWord (A := Alphabet) j).length := by dsimp only [t]; omega
      simp only [hidx] at hone
      have hthree : (shortlexWord j ++ markerRight j)[(shortlexWord (A := Alphabet) j).length]'(by
          simp only [List.length_append]; omega) = 3 := by
        simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, markerRight_three]
      exact (by decide : (3 : Alphabet) ≠ 1) (hthree.symm.trans hone)
    · by_contra h
      let t := p.length + rightOffset k - ((shortlexWord (A := Alphabet) j).length + 1)
      have ht : t < markerLength j := by dsimp only [t]; omega
      have hread := getElem_infix_witness heq (i := rightOffset k)
        (by rw [forbiddenWord_length_rightOffset]; omega)
      have hthree := hread.trans (forbiddenWord_right_three k)
      have hidx : p.length + rightOffset k =
          (shortlexWord (A := Alphabet) j).length + (t + 1) := by dsimp only [t]; omega
      simp only [hidx] at hthree
      have hone : (shortlexWord j ++ markerRight j)[(shortlexWord (A := Alphabet) j).length + (t + 1)]'(by
          simp only [List.length_append]; omega) = 1 := by
        simp only [List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
          markerRight_one j ht]
      exact (by decide : (1 : Alphabet) ≠ 3) (hone.symm.trans hthree)
  have hkj : k = j := Nat.pow_right_injective (by decide : 2 ≤ 5) hr
  subst k
  have hsize := length_forbiddenWord j
  omega
end BalanceSpecification.FiveSymbol
