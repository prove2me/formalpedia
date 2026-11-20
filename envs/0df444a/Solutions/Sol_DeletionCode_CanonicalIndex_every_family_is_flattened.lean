-- Prove2me | solution 1 for DeletionCode.CanonicalIndex.every_family_is_flattened
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:52.830173+00:00
-- url     : https://prove2.me/submissions/24c61307-7bef-4d42-a51c-3ed02b368f44

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_RuleReconstruction
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_DeletionCode_CanonicalIndex

set_option autoImplicit true
open DeletionCode DeletionCode.CanonicalIndex
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport RuleReconstruction
open scoped BigOperators
namespace DeletionCode.CanonicalIndex
theorem _root_.solution {α : Type*} (t R : ℕ) (family : Fin (2 * t * R) → α) :
    ∃ words : Fin R → Fin (2 * t) → α, flatten t R words = family :=
  ⟨unflatten t R family, flatten_unflatten t R family⟩
end DeletionCode.CanonicalIndex
