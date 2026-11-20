-- Prove2me | solution 1 for DeletionCode.CatalogueAlgebra.rational_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:24:05.910831+00:00
-- url     : https://prove2.me/submissions/1cb7843e-2208-449b-aab6-a74dd178df14

import Definitions.Def_DeletionCode_RelationSavings
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Definitions.Def_DeletionCode_CatalogueAlgebra

set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueAlgebra
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks CatalogueBridge
open scoped BigOperators
namespace DeletionCode.CatalogueAlgebra
theorem _root_.solution {L : ℕ} : Function.Injective (@rational L) := by
  intro u v h
  funext g
  have hg : (u g : ℚ) = (v g : ℚ) := congrFun h g
  exact_mod_cast hg
end DeletionCode.CatalogueAlgebra
