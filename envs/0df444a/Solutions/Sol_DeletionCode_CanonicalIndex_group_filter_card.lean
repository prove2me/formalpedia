-- Prove2me | solution 1 for DeletionCode.CanonicalIndex.group_filter_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:53.249437+00:00
-- url     : https://prove2.me/submissions/d3e6bf1d-9fe6-4a75-816e-f6bdc620bd77

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_RuleReconstruction
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_DeletionCode_CanonicalIndex
import Theorems.Thm_DeletionCode_CanonicalIndex_group_fiber_card

set_option autoImplicit true
open DeletionCode DeletionCode.CanonicalIndex
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport RuleReconstruction
open scoped BigOperators
namespace DeletionCode.CanonicalIndex
theorem _root_.solution (t R : ℕ) (r : Fin R) :
    (Finset.univ.filter (fun b : Fin (2 * t * R) => group t R b = r)).card = 2 * t := by
  rw [← Fintype.card_subtype]
  exact group_fiber_card t R r
end DeletionCode.CanonicalIndex
