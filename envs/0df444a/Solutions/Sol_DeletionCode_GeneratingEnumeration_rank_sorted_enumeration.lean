-- Prove2me | solution 1 for DeletionCode.GeneratingEnumeration.rank_sorted_enumeration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:25:48.391581+00:00
-- url     : https://prove2.me/submissions/f38e5315-064a-493b-bc1c-28833537c3de

import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_ManuscriptCounting
import Definitions.Def_DeletionCode_CatalogueFamily
import Mathlib.Data.Finset.Sort
import Definitions.Def_DeletionCode_GeneratingEnumeration
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
theorem _root_.solution {k : ℕ} (G : RuleSet k)
    (rank : (Gram (windowLength k) → ℤ) → ℕ)
    (hinj : Set.InjOn rank (↑G : Set _)) :
    ∃ e : Fin G.card ≃ G, StrictMono (fun i => rank (e i).val) := by
  classical
  let S := G.image rank
  let f : G → S := fun u => ⟨rank u.val, Finset.mem_image.mpr ⟨u.val, u.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      apply Subtype.ext
      exact hinj u.property v.property (congrArg Subtype.val huv)
    · intro r
      obtain ⟨u, hu, hur⟩ := Finset.mem_image.mp r.property
      exact ⟨⟨u, hu⟩, Subtype.ext hur⟩
  let er : G ≃ S := Equiv.ofBijective f hf
  have hcard : S.card = G.card := by
    simpa using Fintype.card_congr er.symm
  let sorted : Fin G.card ≃o S := S.orderIsoOfFin hcard
  let e : Fin G.card ≃ G := sorted.toEquiv.trans er.symm
  have hrank (i : Fin G.card) : rank (e i).val = (sorted i).val := by
    exact congrArg Subtype.val (er.apply_symm_apply (sorted i))
  refine ⟨e, ?_⟩
  intro i j hij
  change rank (e i).val < rank (e j).val
  rw [hrank i, hrank j]
  exact sorted.strictMono hij
end DeletionCode.GeneratingEnumeration
