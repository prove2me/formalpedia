-- Prove2me | solution 1 for DeletionCode.GeneratingEnumeration.exists_ordered_enumeration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:28:08.801916+00:00
-- url     : https://prove2.me/submissions/964536aa-b6f1-4346-9102-845b1759fd41

import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_ManuscriptCounting
import Definitions.Def_DeletionCode_CatalogueFamily
import Mathlib.Data.Finset.Sort
import Definitions.Def_DeletionCode_GeneratingEnumeration
import Theorems.Thm_DeletionCode_GeneratingEnumeration_rank_sorted_enumeration
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk



set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingEnumeration
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport SignedRuleCount RuleReconstruction RuleSetGraph SupportComponents
open CanonicalIndex ConnectedBlocks FiniteGenerating
open scoped BigOperators
namespace DeletionCode.GeneratingEnumeration
theorem _root_.solution {k : ℕ} (v : Gram (windowLength k) → ℤ)
    (G : RuleSet k) (hgen : GeneratingAt v G) :
    ∃ e : Fin G.card ≃ G, ∀ i g, (e i).val g = -1 →
      v g ≠ 0 ∨ ∃ j : Fin G.card, j < i ∧ (e j).val g ≠ 0 := by
  classical
  obtain ⟨rank, hinj, horder⟩ := hgen.ordered
  obtain ⟨e, hmono⟩ := rank_sorted_enumeration G rank hinj
  refine ⟨e, ?_⟩
  intro i g hneg
  rcases horder (e i).val (e i).property g hneg with hv | ⟨z, hz, hrank, hzg⟩
  · exact Or.inl hv
  · let j : Fin G.card := e.symm ⟨z, hz⟩
    have hj : (e j).val = z := by simp [j]
    have hji : j < i := by
      by_contra hnot
      have hij : i ≤ j := le_of_not_gt hnot
      have hrle := hmono.monotone hij
      rw [hj] at hrle
      omega
    exact Or.inr ⟨j, hji, by simpa only [hj] using hzg⟩
end DeletionCode.GeneratingEnumeration
