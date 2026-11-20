-- Prove2me | solution 1 for DeletionCode.CatalogueAlgebra.rational_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:25:09.532413+00:00
-- url     : https://prove2.me/submissions/15479f50-c52b-4b0b-aba8-a76338f0dd1f

import Definitions.Def_DeletionCode_RelationSavings
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk


attribute [local simp] DeletionCode.CatalogueAlgebra.rational_zero

set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueAlgebra
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks CatalogueBridge
open scoped BigOperators
namespace DeletionCode.CatalogueAlgebra
theorem _root_.solution {L : ℕ} (u : Gram L → ℤ) : rational (-u) = -rational u := by
  funext g
  simp [rational]
end DeletionCode.CatalogueAlgebra
