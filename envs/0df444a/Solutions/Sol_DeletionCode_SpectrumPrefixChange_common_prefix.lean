-- Prove2me | solution 1 for DeletionCode.SpectrumPrefixChange.common_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:29.064622+00:00
-- url     : https://prove2.me/submissions/8fe639a8-48cd-4ab5-836a-4e4941f103ab

import Definitions.Def_DeletionCode_SpectrumLocalization
import Definitions.Def_DeletionCode_SpectrumPrefixChange
import Theorems.Thm_DeletionCode_SpectrumLocalization_listLetters_append_left


set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPrefixChange
open Windows CatalogueWords SignedSupport SpectrumLocalization
namespace DeletionCode.SpectrumPrefixChange
theorem _root_.solution (common p q : List Bool) (L : ℕ)
    (hcommon : L - 1 ≤ common.length) :
    Agree (listLetters (common ++ p)) 0 (listLetters (common ++ q)) 0 (L - 1) := by
  intro i hi
  simp only [Nat.zero_add]
  rw [listLetters_append_left common p i (by omega),
    listLetters_append_left common q i (by omega)]
end DeletionCode.SpectrumPrefixChange
