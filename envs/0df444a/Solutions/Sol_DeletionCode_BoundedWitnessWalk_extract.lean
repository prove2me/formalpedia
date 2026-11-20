-- Prove2me | solution 1 for DeletionCode.BoundedWitnessWalk.extract
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:58:06.509902+00:00
-- url     : https://prove2.me/submissions/4c33e789-5ebb-4780-9f58-a15c8d570b55

import Definitions.Def_DeletionCode_WitnessCases
import Definitions.Def_DeletionCode_FiniteWalkRules
import Definitions.Def_DeletionCode_GeneratingEnumeration
import Definitions.Def_DeletionCode_SpectrumPath
import Definitions.Def_DeletionCode_BoundedWitnessWalk
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_mem_selectedBlocks
import Theorems.Thm_DeletionCode_FiniteWalkRules_novelty_transfer
import Theorems.Thm_DeletionCode_FiniteWalkRules_rational_step
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_empty
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_insert
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedSpan_eq
import Theorems.Thm_DeletionCode_FiniteWalkRules_selected_generatingAt
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
import Theorems.Thm_DeletionCode_WalkSelection_odd_boolean_closed_walk_stops
import Theorems.Thm_DeletionCode_WitnessCases_large_block_case
import Theorems.Thm_DeletionCode_WitnessCases_relation_case_of_span
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_neg
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_zero
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.FiniteRelationBlocks.mem_selectedBlocks
attribute [local simp] DeletionCode.FiniteWalkRules.rational_step
attribute [local simp] DeletionCode.FiniteWalkRules.selectedRules_empty
attribute [local simp] DeletionCode.FiniteWalkRules.selectedRules_insert
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk



set_option autoImplicit true
open DeletionCode DeletionCode.BoundedWitnessWalk
open Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open CatalogueAlgebra FiniteWalkRules WalkSelection BlockPartition WitnessCases
namespace DeletionCode.BoundedWitnessWalk
theorem _root_.solution {t k m : ℕ} (ht : 2 ≤ t)
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ)
    (K : Set (Gram (windowLength k) → ℤ))
    (hp : ∀ j, WitnessAlgebra.BooleanVector (rationalPath p j))
    (hclosed : p 0 = p (Fin.last m)) (hodd : Odd m)
    (hcat : ∀ i, CatalogueRule t k (step p i))
    (hK : ∀ i, step p i ∈ K) :
    ∃ U : RuleSet k, Witness t k (p 0) K U := by
  classical
  let Good : Finset (Fin m) → Prop := fun S =>
    ∀ B ∈ blocks (selectedRules p S), B.card ≤ windowLength k
  have hgood : Good ∅ := by simp [Good, blocks]
  have hclosedQ : rationalPath p 0 = rationalPath p (Fin.last m) :=
    congrArg rational hclosed
  obtain ⟨i, S, hs, hgen, hnew, hstop⟩ :=
    odd_boolean_closed_walk_stops (rationalPath p) hp Good hgood hclosedQ hodd
  have hcatS (T : Finset (Fin m)) :
      ∀ u ∈ selectedRules p T, CatalogueRule t k u := by
    intro u hu
    obtain ⟨j, _, rfl⟩ := (mem_selectedRules p T u).mp hu
    exact hcat j
  have hKS (T : Finset (Fin m)) : ∀ u ∈ selectedRules p T, u ∈ K := by
    intro u hu
    obtain ⟨j, _, rfl⟩ := (mem_selectedRules p T u).mp hu
    exact hK j
  rcases hstop with hrel | ⟨_, hind, hbad, hgen'⟩
  · have hspan : rational (step p i) ∈
        Submodule.span ℚ (rational '' (↑(selectedRules p S) : Set _)) := by
      simpa only [rational_step, ← selectedSpan_eq] using hrel
    obtain ⟨U, _, hU⟩ := relation_case_of_span ht (p 0) K (selectedRules p S)
      (selected_generatingAt p S hs.independent hgen) (hcatS S) (hKS S)
      hs.good (step p i) (hcat i) (novelty_transfer p S i hnew) hspan
    exact ⟨U, hU⟩
  · have hgenI : FiniteGenerating.GeneratingAt (p 0)
        (insert (step p i) (selectedRules p S)) := by
      simpa only [selectedRules_insert] using
        selected_generatingAt p (insert i S) hind hgen'
    have hKI : ∀ u ∈ insert (step p i) (selectedRules p S), u ∈ K := by
      simpa only [selectedRules_insert] using hKS (insert i S)
    have hbadI : ¬ ∀ B ∈ blocks (insert (step p i) (selectedRules p S)),
        B.card ≤ windowLength k := by
      simpa only [Good, selectedRules_insert] using hbad
    exact ⟨_, large_block_case ht (p 0) K (selectedRules p S) (step p i)
      hgenI (hcat i) (hcatS S) hKI hs.good hbadI⟩
end DeletionCode.BoundedWitnessWalk
