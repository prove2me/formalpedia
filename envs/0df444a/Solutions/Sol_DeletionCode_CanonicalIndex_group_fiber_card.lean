-- Prove2me | solution 1 for DeletionCode.CanonicalIndex.group_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:38.114622+00:00
-- url     : https://prove2.me/submissions/1b5ed671-f0e8-4c0a-a45c-c716cbca53a9

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_RuleReconstruction
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_DeletionCode_CanonicalIndex

set_option autoImplicit true
open DeletionCode DeletionCode.CanonicalIndex
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport RuleReconstruction
open scoped BigOperators
namespace DeletionCode.CanonicalIndex
theorem _root_.solution (t R : ℕ) (r : Fin R) :
    Fintype.card {b : Fin (2 * t * R) // group t R b = r} = 2 * t := by
  simpa using Fintype.card_congr (groupFiberEquiv t R r)
end DeletionCode.CanonicalIndex
