-- Prove2me | solution 1 for DeletionCode.BubblePathSimplicity.deletion_vertices_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:35.06288+00:00
-- url     : https://prove2.me/submissions/a3f3561a-ce06-428b-b2cf-2fb97c5ad104

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
    (x : Letters) (hx : KUnique x n k) (pos : ℕ) (hpos : pos < n) (s : ℕ)
    (hlength : s + bubble.longWord.length ≤ n)
    (hslength : s + bubble.shortWord.length ≤ n - 1)
    (hlong : Agree (listLetters bubble.longWord) 0 x s bubble.longWord.length)
    (hshort : Agree (listLetters bubble.shortWord) 0 (deleteAt x pos) s bubble.shortWord.length) :
    Function.Injective (fun i : Fin (windowLength k - bubble.rho + 2) =>
      SpectrumPath.vertexAt (listLetters bubble.longWord) (windowLength k) i.val) ∧
    Function.Injective (fun i : Fin (windowLength k - bubble.rho + 1) =>
      SpectrumPath.vertexAt (listLetters bubble.shortWord) (windowLength k) i.val) :=
  bubble_vertices_injective bubble
    (local_word_unique hk x hx .unchanged trivial bubble.longWord s hlength hlong)
    (local_word_unique hk x hx (.delete pos) hpos bubble.shortWord s hslength hshort)
end DeletionCode.BubblePathSimplicity
