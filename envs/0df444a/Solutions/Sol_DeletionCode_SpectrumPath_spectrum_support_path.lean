-- Prove2me | solution 1 for DeletionCode.SpectrumPath.spectrum_support_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:48.619947+00:00
-- url     : https://prove2.me/submissions/10d7b81e-de0e-400f-a941-36c424b6ce6d

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_SpectrumPath
import Theorems.Thm_DeletionCode_SpectrumPath_spectrum_nonzero_iff_occurs

set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators
namespace DeletionCode.SpectrumPath
theorem _root_.solution (word : Letters) (n L : ℕ) (hn : L ≤ n) (g : Gram L) :
    wordSpectrum word n L g ≠ 0 ↔ ∃ i : Fin (n - L + 1), gram word L i.val = g := by
  rw [spectrum_nonzero_iff_occurs]
  constructor
  · rintro ⟨a, ha, hg⟩
    exact ⟨⟨a, by omega⟩, hg⟩
  · rintro ⟨i, hi⟩
    exact ⟨i.val, by have := i.isLt; omega, hi⟩
end DeletionCode.SpectrumPath
