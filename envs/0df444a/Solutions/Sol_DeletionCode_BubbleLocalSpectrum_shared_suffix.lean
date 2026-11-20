-- Prove2me | solution 1 for DeletionCode.BubbleLocalSpectrum.shared_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:23.32208+00:00
-- url     : https://prove2.me/submissions/e8b041ff-bc73-4821-8c07-7d4aa075bb0d

import Definitions.Def_DeletionCode_SpectrumLocalization
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_longWord_length
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_shortWord_length
import Theorems.Thm_DeletionCode_SpectrumLocalization_listLetters_append_right


set_option autoImplicit true
open DeletionCode DeletionCode.BubbleLocalSpectrum
open Windows HeaderRecovery CatalogueWords SignedSupport SpectrumLocalization
namespace DeletionCode.BubbleLocalSpectrum
theorem _root_.solution {k : ℕ} (bubble : BubbleWord k) :
    Agree (listLetters bubble.longWord) (bubble.longWord.length + 1 - windowLength k)
      (listLetters bubble.shortWord) (bubble.shortWord.length + 1 - windowLength k)
      (windowLength k - 1) := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  have hleft := bubble.left_length
  have hlstart : bubble.longWord.length + 1 - windowLength k = bubble.left.length + 1 := by
    rw [bubble.longWord_length]
    simp only [longLength, BubbleWord.header]
    unfold windowLength at *
    omega
  have hsstart : bubble.shortWord.length + 1 - windowLength k = bubble.left.length := by
    rw [bubble.shortWord_length]
    simp only [shortLength, longLength, BubbleWord.header]
    unfold windowLength at *
    omega
  have hrep : List.replicate bubble.rho bubble.bit =
      bubble.bit :: List.replicate (bubble.rho - 1) bubble.bit := by
    conv_lhs => rw [show bubble.rho = (bubble.rho - 1) + 1 by omega, List.replicate_succ]
  rw [hlstart, hsstart]
  intro i _hi
  change listLetters (bubble.left ++ (List.replicate bubble.rho bubble.bit ++ bubble.right))
      (bubble.left.length + 1 + i) =
    listLetters (bubble.left ++ (List.replicate (bubble.rho - 1) bubble.bit ++ bubble.right))
      (bubble.left.length + i)
  have hindex : bubble.left.length + 1 + i = bubble.left.length + (i + 1) := by omega
  rw [hindex, listLetters_append_right, listLetters_append_right, hrep]
  simp only [List.cons_append, listLetters, List.getD_cons_succ]
end DeletionCode.BubbleLocalSpectrum
