-- Prove2me | solution 1 for DeletionCode.CatalogueAlgebra.catalogue_signed_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:26:21.42325+00:00
-- url     : https://prove2.me/submissions/1df44213-75ba-4438-a87a-3c42a2a4ccb4

import Definitions.Def_DeletionCode_RelationSavings
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueBridge_ValidCatalogue_geometry
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
import Theorems.Thm_DeletionCode_WitnessAlgebra_ruleSpectrum_signed_unit
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk


attribute [local simp] DeletionCode.CatalogueAlgebra.rational_zero
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_neg

set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueAlgebra
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks CatalogueBridge
open scoped BigOperators
namespace DeletionCode.CatalogueAlgebra
theorem _root_.solution {t k : ℕ} (u : Gram (windowLength k) → ℤ)
    (hu : CatalogueRule t k u) : WitnessAlgebra.SignedUnitVector (rational u) := by
  classical
  obtain ⟨words, hvalid, _, hvalue⟩ := hu
  have hd : VertexDisjointOn (indexedFamily words (fun _ => (0 : Fin 1))).family
      (windowLength k) Finset.univ := by
    simpa only [Finset.filter_true] using hvalid.within_rule_disjoint (0 : Fin 1)
  have h := WitnessAlgebra.ruleSpectrum_signed_unit _ _ hvalid.geometry Finset.univ hd
  change WitnessAlgebra.SignedUnitVector (fun g => (u g : ℚ))
  simpa only [hvalue] using h
end DeletionCode.CatalogueAlgebra
