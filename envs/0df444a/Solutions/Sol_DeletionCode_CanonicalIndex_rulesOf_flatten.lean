-- Prove2me | solution 1 for DeletionCode.CanonicalIndex.rulesOf_flatten
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:24.938371+00:00
-- url     : https://prove2.me/submissions/c44543a9-48da-45fd-9c71-be314a4c5037

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_RuleReconstruction
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_DeletionCode_CanonicalIndex
import Theorems.Thm_DeletionCode_CanonicalIndex_flat_rule_spectrum

set_option autoImplicit true
open DeletionCode DeletionCode.CanonicalIndex
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport RuleReconstruction
open scoped BigOperators
namespace DeletionCode.CanonicalIndex
theorem _root_.solution {k : ℕ} (t R : ℕ) (words : Fin R → Fin (2 * t) → BubbleWord k) :
    rulesOfFamily (flatFamily t R words) (group t R) =
      Finset.univ.image (fun r : Fin R => fun g =>
        ∑ j : Fin (2 * t), bubbleSpectrum (pairFamily t R words).family (windowLength k) (r, j) g) := by
  classical
  unfold rulesOfFamily
  apply Finset.image_congr
  intro r hr
  exact flat_rule_spectrum t R words r
end DeletionCode.CanonicalIndex
