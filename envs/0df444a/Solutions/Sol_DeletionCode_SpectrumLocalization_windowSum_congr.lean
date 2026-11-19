-- Prove2me | solution 1 for DeletionCode.SpectrumLocalization.windowSum_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:34:27.72529+00:00
-- url     : https://prove2.me/submissions/9b78ea84-e4ca-481b-aeb4-eb95bbdf784d

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_DeletionCode_SpectrumLocalization

set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators
namespace DeletionCode.SpectrumLocalization
theorem _root_.solution (x y : Letters) (L a b count : ℕ) (g : Gram L)
    (h : ∀ i, i < count → gram x L (a + i) = gram y L (b + i)) :
    windowSum x L a count g = windowSum y L b count g := by
  classical
  unfold windowSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i (Finset.mem_range.mp hi)]
end DeletionCode.SpectrumLocalization
