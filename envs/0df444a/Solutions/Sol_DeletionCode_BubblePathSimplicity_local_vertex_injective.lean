-- Prove2me | solution 1 for DeletionCode.BubblePathSimplicity.local_vertex_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:35.958552+00:00
-- url     : https://prove2.me/submissions/edb94111-9b51-4d3e-9954-645b9f951caa

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_BubblePathSimplicity
import Theorems.Thm_DeletionCode_BubblePathSimplicity_local_word_unique
import Theorems.Thm_DeletionCode_SpectrumPath_vertex_path_injective


set_option autoImplicit true
open DeletionCode DeletionCode.BubblePathSimplicity
open Windows HeaderRecovery CatalogueWords SingleEditOrigins
namespace DeletionCode.BubblePathSimplicity
theorem _root_.solution {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (e : Edit) (he : e.Valid n)
    (word : List Bool) (s : ℕ)
    (hbound : s + word.length ≤ e.outputLength n)
    (hocc : Agree (listLetters word) 0 (e.word x) s word.length)
    (hlength : windowLength k ≤ word.length) :
    Function.Injective (fun i : Fin (word.length - windowLength k + 2) =>
      SpectrumPath.vertexAt (listLetters word) (windowLength k) i.val) :=
  SpectrumPath.vertex_path_injective (listLetters word) word.length (windowLength k)
    (by unfold windowLength; omega) hlength
    (local_word_unique hk x hx e he word s hbound hocc)
end DeletionCode.BubblePathSimplicity
