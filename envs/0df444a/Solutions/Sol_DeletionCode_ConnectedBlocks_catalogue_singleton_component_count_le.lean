-- Prove2me | solution 1 for DeletionCode.ConnectedBlocks.catalogue_singleton_component_count_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:09.994172+00:00
-- url     : https://prove2.me/submissions/776e6acc-bd5d-45ef-ace4-592f4f6c3e87

import Definitions.Def_DeletionCode_ComponentBounds
import Definitions.Def_DeletionCode_CatalogueBridge
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
import Definitions.Def_DeletionCode_ConnectedBlocks
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
import Theorems.Thm_DeletionCode_CatalogueBridge_ValidCatalogue_geometry
import Theorems.Thm_DeletionCode_CatalogueBridge_ValidCatalogue_rank_disjoint
import Theorems.Thm_DeletionCode_GeneratingCount_editedFamily_component_count_le
import Theorems.Thm_DeletionCode_RuleSetGraph_componentCount_rulesOfFamily

section
namespace DeletionCode.ConnectedBlocks
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport SignedRuleCount RuleReconstruction RuleSetGraph
private theorem singleton_rules {t k : ℕ} (words : Fin (2 * t) → BubbleWord k)
    (w : Gram (windowLength k) → ℤ)
    (hvalue : ruleSpectrum (indexedFamily words (fun _ => (0 : Fin 1))).family
      (windowLength k) Finset.univ = w) :
    rulesOfFamily (indexedFamily words (fun _ => (0 : Fin 1)))
      (fun _ => (0 : Fin 1)) = {w} := by
  classical
  have hgroup (r : Fin 1) :
      groupBubbles (fun _ : Fin (2 * t) => (0 : Fin 1)) r = Finset.univ := by
    have hr : r = 0 := Subsingleton.elim _ _
    subst r
    simp [groupBubbles]
  ext f
  simp only [rulesOfFamily, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨r, hf⟩
    rw [hgroup r, hvalue] at hf
    exact hf.symm
  · intro hf
    refine ⟨0, ?_⟩
    rw [hgroup 0, hvalue, hf]
end DeletionCode.ConnectedBlocks
end

set_option autoImplicit true
open DeletionCode DeletionCode.ConnectedBlocks
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport SignedRuleCount RuleReconstruction RuleSetGraph
namespace DeletionCode.ConnectedBlocks
theorem _root_.solution {t k : ℕ}
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w) :
    componentCount {w} ≤ 2 * t := by
  obtain ⟨words, hvalid, _, hvalue⟩ := hw
  rw [← singleton_rules words w hvalue]
  rw [componentCount_rulesOfFamily
    (indexedFamily words (fun _ => (0 : Fin 1))) (fun _ => (0 : Fin 1))
    (fun _ => rfl) hvalid.geometry hvalid.rank_disjoint]
  exact GeneratingCount.editedFamily_component_count_le
    (indexedFamily words (fun _ => (0 : Fin 1)))
end DeletionCode.ConnectedBlocks
