-- Prove2me | solution 1 for DeletionCode.CanonicalIndex.flat_bubble_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:39.675362+00:00
-- url     : https://prove2.me/submissions/0a34a4cd-3767-4795-b8bd-e6bbe837395d

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_RuleReconstruction
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_DeletionCode_CanonicalIndex

set_option autoImplicit true
open DeletionCode DeletionCode.CanonicalIndex
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport RuleReconstruction
open scoped BigOperators
namespace DeletionCode.CanonicalIndex
theorem _root_.solution {k : ℕ} (t R : ℕ)
    (words : Fin R → Fin (2 * t) → BubbleWord k) (b : Fin (2 * t * R)) :
    bubbleSpectrum (flatFamily t R words).family (windowLength k) b =
      bubbleSpectrum (pairFamily t R words).family (windowLength k) (indexEquiv t R b) := rfl
end DeletionCode.CanonicalIndex
