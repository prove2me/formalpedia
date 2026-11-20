-- Prove2me | solution 1 for DeletionCode.SpectrumLocalization.windowSum_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:21.611634+00:00
-- url     : https://prove2.me/submissions/88880e88-0cbf-4732-8d15-94569ce361de

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_DeletionCode_SpectrumLocalization

set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators
namespace DeletionCode.SpectrumLocalization
theorem _root_.solution (x : Letters) (L start a b : ℕ) (g : Gram L) :
    windowSum x L start (a + b) g =
      windowSum x L start a g + windowSum x L (start + a) b g := by
  classical
  unfold windowSum
  rw [Finset.sum_range_add]
  simp only [Nat.add_assoc]
end DeletionCode.SpectrumLocalization
