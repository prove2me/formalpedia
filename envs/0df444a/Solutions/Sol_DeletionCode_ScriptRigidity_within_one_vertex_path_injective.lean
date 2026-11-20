-- Prove2me | solution 1 for DeletionCode.ScriptRigidity.within_one_vertex_path_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:31.88083+00:00
-- url     : https://prove2.me/submissions/517cad68-95c4-4da7-b480-8c42751c9020

import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_ScriptRigidity
import Theorems.Thm_DeletionCode_ScriptRigidity_within_one_unique
import Theorems.Thm_DeletionCode_SpectrumPath_vertex_path_injective


set_option autoImplicit true
open DeletionCode DeletionCode.ScriptRigidity
open Windows HeaderRecovery CatalogueWords EditAlignment SingleEditOrigins
namespace DeletionCode.ScriptRigidity
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (x y : List Bool)
    (hx : KUnique (listLetters x) x.length k) (hy : WithinEdits 1 x y)
    (hlen : windowLength k ≤ y.length) :
    Function.Injective (fun i : Fin (y.length - windowLength k + 2) =>
      SpectrumPath.vertexAt (listLetters y) (windowLength k) i.val) :=
  SpectrumPath.vertex_path_injective (listLetters y) y.length (windowLength k)
    (by unfold windowLength; omega) hlen (within_one_unique hk x y hx hy)
end DeletionCode.ScriptRigidity
