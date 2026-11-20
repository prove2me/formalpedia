-- Prove2me | solution 1 for DeletionCode.ScriptRigidity.within_one_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:40.838723+00:00
-- url     : https://prove2.me/submissions/c39dda21-254a-4f0d-93ea-fc5d62953408

import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_ScriptRigidity
import Theorems.Thm_DeletionCode_EditRigidity_one_edit_unique
import Theorems.Thm_DeletionCode_SingleEditScripts_within_one_realized


set_option autoImplicit true
open DeletionCode DeletionCode.ScriptRigidity
open Windows HeaderRecovery CatalogueWords EditAlignment SingleEditOrigins
namespace DeletionCode.ScriptRigidity
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (x y : List Bool)
    (hx : KUnique (listLetters x) x.length k) (hy : WithinEdits 1 x y) :
    KUnique (listLetters y) y.length (windowLength k - 1) := by
  obtain ⟨e, he, hlen, hword⟩ := SingleEditScripts.within_one_realized hy
  simpa only [hlen, hword] using EditRigidity.one_edit_unique hk (listLetters x) hx e he
end DeletionCode.ScriptRigidity
