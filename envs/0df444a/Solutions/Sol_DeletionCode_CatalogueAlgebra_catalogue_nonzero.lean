-- Prove2me | solution 1 for DeletionCode.CatalogueAlgebra.catalogue_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:26:22.044035+00:00
-- url     : https://prove2.me/submissions/534dd5f5-9d59-4f8f-afd6-b322f8116484

import Definitions.Def_DeletionCode_RelationSavings
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueBridge_ValidCatalogue_geometry
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_SignedSupport_rule_negative_of_window
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk


attribute [local simp] DeletionCode.CatalogueAlgebra.rational_zero
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_neg

set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueAlgebra
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks CatalogueBridge
open scoped BigOperators
namespace DeletionCode.CatalogueAlgebra
theorem _root_.solution {t k : ℕ} (ht : 1 ≤ t)
    (u : Gram (windowLength k) → ℤ) (hu : CatalogueRule t k u) : u ≠ 0 := by
  classical
  obtain ⟨words, hvalid, _, hvalue⟩ := hu
  let E := indexedFamily words (fun _ => (0 : Fin 1))
  let b : Fin (2 * t) := ⟨0, by omega⟩
  have hd : VertexDisjointOn E.family (windowLength k) Finset.univ := by
    simpa only [Finset.filter_true] using hvalid.within_rule_disjoint (0 : Fin 1)
  let g := gram (E.family.path b false) (windowLength k) 0
  have hgram : g ∈ windowSet (E.family.path b false) (windowLength k)
      (E.family.extra b false) := ⟨⟨0, by omega⟩, rfl⟩
  have hneg := rule_negative_of_window E.family (windowLength k) hvalid.geometry
    Finset.univ hd b (Finset.mem_univ b) g hgram
  rw [hvalue] at hneg
  intro hz
  rw [hz] at hneg
  norm_num at hneg
end DeletionCode.CatalogueAlgebra
