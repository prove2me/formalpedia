-- Prove2me | solution 1 for DeletionCode.TraceSpectrumAssembly.spectrum_sum_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:01:07.495968+00:00
-- url     : https://prove2.me/submissions/6f8b1e73-494a-4ce6-8df1-147eb396e29c

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceMatchedSuffix
import Definitions.Def_DeletionCode_SpectrumPrefixChange
import Definitions.Def_DeletionCode_TraceSpectrumAssembly
import Theorems.Thm_DeletionCode_TraceSpectrumAssembly_hybrid_increment_of_not_edit
import Theorems.Thm_DeletionCode_TraceSpectrumAssembly_hybrid_increment_of_edit
import Theorems.Thm_DeletionCode_TraceSpectrumAssembly_hybrid_telescope
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_end
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_zero
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
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
open DeletionCode DeletionCode.TraceSpectrumAssembly
open AlignmentTrace FiniteConflictGraph TraceEditData SignedSupport
open SpectrumPrefixChange TraceMatchedSuffix
open scoped BigOperators
namespace DeletionCode.TraceSpectrumAssembly
theorem _root_.solution {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (g : Gram L) :
    spectrum trace.target L g - spectrum trace.source L g =
      ∑ c : EditColumn trace,
        (spectrum (oneEditTarget trace c) L g - spectrum trace.source L g) := by
  classical
  let : Fintype {i : Fin trace.length // EditIndex trace i} := editColumnFintype trace
  let F : Fin trace.length → ℤ := fun i =>
    spectrum (hybrid trace (i.val + 1)) L g - spectrum (hybrid trace i.val) L g
  have hrestrict : (∑ i : Fin trace.length, F i) = ∑ c : EditColumn trace, F c.val := by
    change _ = ∑ c : {i : Fin trace.length // EditIndex trace i}, F c.val
    rw [← Finset.sum_subtype (Finset.univ.filter (fun i => EditIndex trace i)) (by simp) F]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hnot
    apply hybrid_increment_of_not_edit trace i _ L g
    intro hi
    exact hnot (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi)
  calc
    spectrum trace.target L g - spectrum trace.source L g = ∑ i : Fin trace.length, F i :=
      hybrid_telescope trace L g
    _ = ∑ c : EditColumn trace, F c.val := hrestrict
    _ = ∑ c : EditColumn trace,
        (spectrum (oneEditTarget trace c) L g - spectrum trace.source L g) := by
      apply Finset.sum_congr rfl
      intro c _
      exact hybrid_increment_of_edit hL hsep c g
end DeletionCode.TraceSpectrumAssembly
