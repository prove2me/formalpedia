-- Prove2me | solution 1 for DeletionCode.BubblePathSimplicity.bubble_vertices_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:38:39.4473+00:00
-- url     : https://prove2.me/submissions/98322e27-d59a-4b64-ad3e-d24e37c9a457

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_BubblePathSimplicity
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_longWord_length
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_shortWord_length


set_option autoImplicit true
open DeletionCode DeletionCode.BubblePathSimplicity
open Windows HeaderRecovery CatalogueWords SingleEditOrigins
namespace DeletionCode.BubblePathSimplicity
theorem _root_.solution {k : ℕ} (bubble : BubbleWord k)
    (hlong : KUnique (listLetters bubble.longWord) bubble.longWord.length (windowLength k - 1))
    (hshort : KUnique (listLetters bubble.shortWord) bubble.shortWord.length (windowLength k - 1)) :
    Function.Injective (fun i : Fin (windowLength k - bubble.rho + 2) =>
      SpectrumPath.vertexAt (listLetters bubble.longWord) (windowLength k) i.val) ∧
    Function.Injective (fun i : Fin (windowLength k - bubble.rho + 1) =>
      SpectrumPath.vertexAt (listLetters bubble.shortWord) (windowLength k) i.val) := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  have hlonglen : bubble.longWord.length = 2 * windowLength k - bubble.rho := by
    simpa only [longLength, BubbleWord.header] using bubble.longWord_length
  have hshortlen : bubble.shortWord.length = 2 * windowLength k - bubble.rho - 1 := by
    simpa only [shortLength, longLength, BubbleWord.header] using bubble.shortWord_length
  have hL : 1 ≤ windowLength k := by unfold windowLength; omega
  have hlongbound : windowLength k ≤ bubble.longWord.length := by
    unfold windowLength at *
    omega
  have hshortbound : windowLength k ≤ bubble.shortWord.length := by
    unfold windowLength at *
    omega
  have hlongcount : bubble.longWord.length - windowLength k + 2 =
      windowLength k - bubble.rho + 2 := by
    unfold windowLength at *
    omega
  have hshortcount : bubble.shortWord.length - windowLength k + 2 =
      windowLength k - bubble.rho + 1 := by
    unfold windowLength at *
    omega
  constructor
  · intro i j heq
    apply Fin.ext
    apply hlong i.val j.val
    · have hi := i.isLt
      omega
    · have hj := j.isLt
      omega
    · intro r hr
      exact congrFun heq ⟨r, hr⟩
  · intro i j heq
    apply Fin.ext
    apply hshort i.val j.val
    · have hi := i.isLt
      omega
    · have hj := j.isLt
      omega
    · intro r hr
      exact congrFun heq ⟨r, hr⟩
end DeletionCode.BubblePathSimplicity
