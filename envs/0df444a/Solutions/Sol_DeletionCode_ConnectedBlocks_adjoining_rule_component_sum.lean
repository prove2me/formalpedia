-- Prove2me | solution 1 for DeletionCode.ConnectedBlocks.adjoining_rule_component_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:22:37.814975+00:00
-- url     : https://prove2.me/submissions/a60db59c-2017-448f-954b-74f2c3e8bef7

import Definitions.Def_DeletionCode_ComponentBounds
import Definitions.Def_DeletionCode_CatalogueBridge
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
import Definitions.Def_DeletionCode_ConnectedBlocks
import Theorems.Thm_DeletionCode_ConnectedBlocks_catalogue_singleton_component_count_le
import Theorems.Thm_DeletionCode_ComponentBounds_componentCount_union_add_one_le


set_option autoImplicit true
open DeletionCode DeletionCode.ConnectedBlocks
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport SignedRuleCount RuleReconstruction RuleSetGraph
namespace DeletionCode.ConnectedBlocks
theorem _root_.solution {t k : ℕ}
    (U : RuleSet k) (w : Gram (windowLength k) → ℤ)
    (hw : CatalogueRule t k w) (hadj : ∃ u ∈ U, RuleAdjacent w u) :
    componentCount (insert w U) + 1 ≤ componentCount U + 2 * t := by
  classical
  obtain ⟨u, hu, v, hvw, hvu⟩ := hadj
  have hsub : ({u} : RuleSet k) ⊆ U := by
    intro a ha
    have hau : a = u := Finset.mem_singleton.mp ha
    simpa only [hau] using hu
  have hmeet : ∃ v, Incident U v ∧ Incident {w} v :=
    ⟨v, ComponentBounds.incident_mono hsub hvu, hvw⟩
  have h := ComponentBounds.componentCount_union_add_one_le U {w} hmeet
  have heq : U ∪ {w} = insert w U := by
    ext a
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
    exact or_comm
  rw [heq] at h
  exact h.trans (Nat.add_le_add_left (catalogue_singleton_component_count_le w hw) _)
end DeletionCode.ConnectedBlocks
