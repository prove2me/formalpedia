-- Prove2me | solution 1 for DeletionCode.ScriptRigidity.within_one_spectrum_boolean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:31.432772+00:00
-- url     : https://prove2.me/submissions/eb409a34-a25c-4425-be95-73c6c6e6b8e0

import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_ScriptRigidity
import Theorems.Thm_DeletionCode_ScriptRigidity_within_one_unique
import Theorems.Thm_DeletionCode_SpectrumPath_spectrum_boolean


set_option autoImplicit true
open DeletionCode DeletionCode.ScriptRigidity
open Windows HeaderRecovery CatalogueWords EditAlignment SingleEditOrigins
namespace DeletionCode.ScriptRigidity
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (x y : List Bool)
    (hx : KUnique (listLetters x) x.length k) (hy : WithinEdits 1 x y) :
    ∀ g, SignedSupport.wordSpectrum (listLetters y) y.length (windowLength k) g = 0 ∨
      SignedSupport.wordSpectrum (listLetters y) y.length (windowLength k) g = 1 :=
  SpectrumPath.spectrum_boolean (listLetters y) y.length (windowLength k)
    (within_one_unique hk x y hx hy)
end DeletionCode.ScriptRigidity
