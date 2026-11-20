-- Prove2me | solution 1 for DeletionCode.BubblePathSimplicity.insertion_vertices_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:35.548123+00:00
-- url     : https://prove2.me/submissions/b0f38850-0865-4ce0-8864-5055e16e4420

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_BubblePathSimplicity
import Theorems.Thm_DeletionCode_BubblePathSimplicity_local_word_unique
import Theorems.Thm_DeletionCode_BubblePathSimplicity_bubble_vertices_injective

set_option autoImplicit true
open DeletionCode DeletionCode.BubblePathSimplicity
open Windows HeaderRecovery CatalogueWords SingleEditOrigins
namespace DeletionCode.BubblePathSimplicity
theorem _root_.solution {n k : ℕ} (hk : 1 ≤ k) (bubble : BubbleWord k)
    (x : Letters) (hx : KUnique x n k) (pos : ℕ) (bit : Bool) (hpos : pos ≤ n) (s : ℕ)
    (hlength : s + bubble.longWord.length ≤ n + 1)
    (hslength : s + bubble.shortWord.length ≤ n)
    (hlong : Agree (listLetters bubble.longWord) 0 (insertAt x pos bit) s bubble.longWord.length)
    (hshort : Agree (listLetters bubble.shortWord) 0 x s bubble.shortWord.length) :
    Function.Injective (fun i : Fin (windowLength k - bubble.rho + 2) =>
      SpectrumPath.vertexAt (listLetters bubble.longWord) (windowLength k) i.val) ∧
    Function.Injective (fun i : Fin (windowLength k - bubble.rho + 1) =>
      SpectrumPath.vertexAt (listLetters bubble.shortWord) (windowLength k) i.val) :=
  bubble_vertices_injective bubble
    (local_word_unique hk x hx (.insert pos bit) hpos bubble.longWord s hlength hlong)
    (local_word_unique hk x hx .unchanged trivial bubble.shortWord s hslength hshort)
end DeletionCode.BubblePathSimplicity
