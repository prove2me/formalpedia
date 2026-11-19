-- Prove2me | solution 1 for DeletionCode.BubbleEndpoints.endpoints_of_displacement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:35:01.763208+00:00
-- url     : https://prove2.me/submissions/9c489062-1c96-4350-8a84-8c13549023ef

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_BubbleEndpoints
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_delete_longWord

section
namespace DeletionCode.BubbleEndpoints
open Windows HeaderRecovery CatalogueWords SingleEditOrigins
private theorem long_first_run {k : ℕ} (bubble : BubbleWord k) :
    listLetters bubble.longWord (windowLength k - bubble.rho) = bubble.bit := by
  have hlo := bubble.rho_lower
  simp only [listLetters, BubbleWord.longWord, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by rw [bubble.left_length])]
  rw [bubble.left_length, Nat.sub_self]
  rw [List.getElem?_append_left (by simp only [List.length_replicate]; omega)]
  rw [List.getElem?_replicate_of_lt (by omega)]
  rfl
private theorem long_first_right {k : ℕ} (bubble : BubbleWord k)
    (hright : bubble.right.head? = some (!bubble.bit)) :
    listLetters bubble.longWord (windowLength k) = !bubble.bit := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  have hlength := bubble.left_length
  have hindex : windowLength k - bubble.left.length = bubble.rho := by
    unfold windowLength at *
    omega
  simp only [listLetters, BubbleWord.longWord, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), hindex]
  rw [List.getElem?_append_right (by simp only [List.length_replicate]; omega)]
  simp only [List.length_replicate, Nat.sub_self]
  rw [← List.head?_eq_getElem?, hright]
  rfl
private theorem short_first_right {k : ℕ} (bubble : BubbleWord k)
    (hright : bubble.right.head? = some (!bubble.bit)) :
    listLetters bubble.shortWord (windowLength k - 1) = !bubble.bit := by
  rw [← bubble.delete_longWord]
  have hpos : 0 < windowLength k := by unfold windowLength; omega
  simp only [deleteAt, editOffset, lt_self_iff_false, ite_false]
  have hindex : windowLength k - 1 + 1 = windowLength k := by omega
  rw [hindex]
  exact long_first_right bubble hright
private theorem short_last_left {k : ℕ} (bubble : BubbleWord k)
    (hleft : bubble.left.getLast? = some (!bubble.bit)) :
    listLetters bubble.shortWord (windowLength k - bubble.rho - 1) = !bubble.bit := by
  have hhi := bubble.rho_upper
  have hlength := bubble.left_length
  have hindex : windowLength k - bubble.rho - 1 = bubble.left.length - 1 := by
    rw [hlength]
  have hbound : windowLength k - bubble.rho - 1 < bubble.left.length := by
    unfold windowLength at *
    omega
  simp only [listLetters, BubbleWord.shortWord, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hbound, hindex, ← List.getLast?_eq_getElem?, hleft]
  rfl
end DeletionCode.BubbleEndpoints
end

set_option autoImplicit true
open DeletionCode DeletionCode.BubbleEndpoints
open Windows HeaderRecovery CatalogueWords SingleEditOrigins
namespace DeletionCode.BubbleEndpoints
theorem _root_.solution {k : ℕ} (bubble : BubbleWord k)
    (hleft : bubble.left.getLast? = some (!bubble.bit))
    (hright : bubble.right.head? = some (!bubble.bit))
    (a b : ℕ) (_ha : a ≤ windowLength k - bubble.rho + 1)
    (hb : b ≤ windowLength k - bubble.rho)
    (hag : Agree (listLetters bubble.longWord) a
      (listLetters bubble.shortWord) b (windowLength k - 1))
    (hdis : a = b ∨ a = b + 1) :
    (a = 0 ∧ b = 0) ∨
      (a = windowLength k - bubble.rho + 1 ∧ b = windowLength k - bubble.rho) := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  have hL : 0 < windowLength k := by unfold windowLength; omega
  have hne : bubble.bit ≠ !bubble.bit := by cases bubble.bit <;> decide
  rcases hdis with heq | heq
  · have ha0 : a = 0 := by
      by_contra hnot
      have hoff : windowLength k - 1 - a < windowLength k - 1 := by omega
      have hindex : a + (windowLength k - 1 - a) = windowLength k - 1 := by omega
      have hindex' : b + (windowLength k - 1 - a) = windowLength k - 1 := by omega
      have hbits := hag _ hoff
      rw [hindex, hindex'] at hbits
      have hrun : listLetters bubble.longWord (windowLength k - 1) = bubble.bit :=
        bubble.header_bit
      rw [hrun, short_first_right bubble hright] at hbits
      exact hne hbits
    exact Or.inl ⟨ha0, by omega⟩
  · have hbLast : b = windowLength k - bubble.rho := by
      by_contra hnot
      have hoff : windowLength k - bubble.rho - 1 - b < windowLength k - 1 := by omega
      have hindex : a + (windowLength k - bubble.rho - 1 - b) =
          windowLength k - bubble.rho := by omega
      have hindex' : b + (windowLength k - bubble.rho - 1 - b) =
          windowLength k - bubble.rho - 1 := by omega
      have hbits := hag _ hoff
      rw [hindex, hindex', long_first_run bubble, short_last_left bubble hleft] at hbits
      exact hne hbits
    exact Or.inr ⟨by omega, hbLast⟩
end DeletionCode.BubbleEndpoints
