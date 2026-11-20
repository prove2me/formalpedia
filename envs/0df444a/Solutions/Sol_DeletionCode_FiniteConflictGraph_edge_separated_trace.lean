-- Prove2me | solution 1 for DeletionCode.FiniteConflictGraph.edge_separated_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:38:31.174914+00:00
-- url     : https://prove2.me/submissions/a4b9eeeb-2e74-46c9-b9cf-bc34d0823f31

import Definitions.Def_DeletionCode_AlignmentTrace
import Definitions.Def_DeletionCode_BoundedWitnessWalk
import Mathlib.Combinatorics.SimpleGraph.Basic
import Definitions.Def_DeletionCode_FiniteConflictGraph
import Theorems.Thm_DeletionCode_FiniteConflictGraph_nonexceptional_trace
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_end
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_zero
import Theorems.Thm_DeletionCode_AlignmentTrace_trace_of_equal_length_confusability
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_mem_selectedBlocks
import Theorems.Thm_DeletionCode_FiniteWalkRules_rational_step
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_empty
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_insert
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.AlignmentTrace.Trace.matchedAnchor_end
attribute [local simp] DeletionCode.AlignmentTrace.Trace.matchedAnchor_zero
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
open DeletionCode DeletionCode.FiniteConflictGraph
open HeaderRecovery AlignmentTrace EditAlignment
variable {n : ℕ} {H : Type*}
namespace DeletionCode.FiniteConflictGraph
theorem _root_.solution {t k : ℕ} {label : Bits n → H}
    {x y : Vertex t k label} (hxy : (graph t k label).Adj x y) :
    ∃ trace : Trace,
      trace.source = List.ofFn x.val ∧ trace.target = List.ofFn y.val ∧
      trace.deletions = t ∧ trace.insertions = t ∧
      Separated (4 * windowLength k) trace := by
  obtain ⟨output, hxout, hyout⟩ := hxy.2.1
  obtain ⟨d, trace, hd, hs, ht, hdel, hins⟩ :=
    trace_of_equal_length_confusability (List.ofFn x.val) (List.ofFn y.val)
      output n t (by simp) (by simp) hxout hyout
  have hfull := nonexceptional_trace x y.val hxy.1 hxy.2.2 d trace hd hs ht hdel hins
  exact ⟨trace, hs, ht, hfull⟩
end DeletionCode.FiniteConflictGraph
