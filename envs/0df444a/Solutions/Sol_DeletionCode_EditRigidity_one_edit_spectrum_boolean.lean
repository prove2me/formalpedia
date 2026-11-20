-- Prove2me | solution 1 for DeletionCode.EditRigidity.one_edit_spectrum_boolean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:43.892852+00:00
-- url     : https://prove2.me/submissions/671c9588-c227-493d-bbd9-b74f994d8801

import Definitions.Def_DeletionCode_SingleEditOrigins
import Definitions.Def_DeletionCode_TwoEditWindows
import Definitions.Def_DeletionCode_SpectrumPath
import Definitions.Def_DeletionCode_EditRigidity
import Theorems.Thm_DeletionCode_EditRigidity_one_edit_unique
import Theorems.Thm_DeletionCode_SpectrumPath_spectrum_boolean


set_option autoImplicit true
open DeletionCode DeletionCode.EditRigidity
open Windows HeaderRecovery SingleEditOrigins
namespace DeletionCode.EditRigidity
theorem _root_.solution {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (e : Edit) (he : e.Valid n) :
    ∀ g, SignedSupport.wordSpectrum (e.word x) (e.outputLength n) (windowLength k) g = 0 ∨
      SignedSupport.wordSpectrum (e.word x) (e.outputLength n) (windowLength k) g = 1 :=
  SpectrumPath.spectrum_boolean (e.word x) (e.outputLength n) (windowLength k)
    (one_edit_unique hk x hx e he)
end DeletionCode.EditRigidity
