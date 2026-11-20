-- Prove2me | solution 1 for DeletionCode.SpectrumLocalization.windowSum_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:22.051267+00:00
-- url     : https://prove2.me/submissions/5f2e30fc-a5df-442a-8200-dece57fef058

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_DeletionCode_SpectrumLocalization

set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators
namespace DeletionCode.SpectrumLocalization
theorem _root_.solution (x : Letters) (L a count : ℕ) (g : Gram L) :
    windowSum x L a count g = windowSum (fun i => x (a + i)) L 0 count g := by
  classical
  unfold windowSum
  apply Finset.sum_congr rfl
  intro i _
  have hgram : gram x L (a + i) = gram (fun j => x (a + j)) L (0 + i) := by
    funext j
    simp only [SignedSupport.gram, Nat.zero_add, Nat.add_assoc]
  rw [hgram]
end DeletionCode.SpectrumLocalization
