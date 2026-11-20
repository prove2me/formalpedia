-- Prove2me | solution 1 for DeletionCode.SpectrumLocalization.listLetters_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:22.452009+00:00
-- url     : https://prove2.me/submissions/5658c36a-1175-40ae-a4ff-d4ab4cf70b6e

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_DeletionCode_SpectrumLocalization
import Theorems.Thm_DeletionCode_SpectrumLocalization_listLetters_append_right

set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators
namespace DeletionCode.SpectrumLocalization
theorem _root_.solution (x p y : List Bool) (i : ℕ) :
    listLetters (x ++ (p ++ y)) (x.length + p.length + i) = listLetters y i := by
  rw [Nat.add_assoc, listLetters_append_right, listLetters_append_right]
end DeletionCode.SpectrumLocalization
