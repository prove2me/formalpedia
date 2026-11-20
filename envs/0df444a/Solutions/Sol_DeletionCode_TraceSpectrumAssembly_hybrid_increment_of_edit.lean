-- Prove2me | solution 1 for DeletionCode.TraceSpectrumAssembly.hybrid_increment_of_edit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:58:51.034237+00:00
-- url     : https://prove2.me/submissions/4489856e-80f1-4013-b929-55f61dd84d73

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceMatchedSuffix
import Definitions.Def_DeletionCode_SpectrumPrefixChange
import Definitions.Def_DeletionCode_TraceSpectrumAssembly
import Theorems.Thm_DeletionCode_TraceSpectrumAssembly_hybrid_before
import Theorems.Thm_DeletionCode_TraceSpectrumAssembly_hybrid_after
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_end
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_zero
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
import Theorems.Thm_DeletionCode_SpectrumPrefixChange_common_suffix_change
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
import Theorems.Thm_DeletionCode_TraceEditData_oneEditTarget_deletion_split
import Theorems.Thm_DeletionCode_TraceEditData_oneEditTarget_insertion_split
import Theorems.Thm_DeletionCode_TraceEditData_source_split_of_deletion
import Theorems.Thm_DeletionCode_TraceEditData_source_split_of_insertion
import Theorems.Thm_DeletionCode_TraceMatchedSuffix_common_suffix_before_edit
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
    (hsep : Separated (4 * L) trace) (c : EditColumn trace) (g : Gram L) :
    spectrum (hybrid trace (c.val.val + 1)) L g - spectrum (hybrid trace c.val.val) L g =
      spectrum (oneEditTarget trace c) L g - spectrum trace.source L g := by
  obtain ⟨a, b, common, hs, ht, hcommon⟩ := common_suffix_before_edit hL hsep c.val c.property
  change sourcePrefix trace c = a ++ common at hs
  change targetPrefix trace c = b ++ common at ht
  rcases column_cases trace c with ⟨bit, hc⟩ | ⟨bit, hc⟩
  · have hc' : trace.get c.val = .deletion bit := hc
    have hbefore : hybrid trace c.val.val = targetPrefix trace c ++ bit :: sourceSuffix trace c := by
      simpa only [targetPrefix, sourceSuffix, hc', Trace.source, List.singleton_append] using
        hybrid_before trace c.val
    have hafter : hybrid trace (c.val.val + 1) = targetPrefix trace c ++ sourceSuffix trace c := by
      simpa only [targetPrefix, sourceSuffix, hc', Trace.target, List.append_nil] using
        hybrid_after trace c.val
    rw [hbefore, hafter, oneEditTarget_deletion_split trace c bit hc,
      source_split_of_deletion trace c bit hc, hs, ht]
    exact common_suffix_change a b common (bit :: sourceSuffix trace c)
      (sourceSuffix trace c) L hL hcommon g
  · have hc' : trace.get c.val = .insertion bit := hc
    have hbefore : hybrid trace c.val.val = targetPrefix trace c ++ sourceSuffix trace c := by
      simpa only [targetPrefix, sourceSuffix, hc', Trace.source, List.nil_append] using
        hybrid_before trace c.val
    have hafter : hybrid trace (c.val.val + 1) = targetPrefix trace c ++ bit :: sourceSuffix trace c := by
      simpa only [targetPrefix, sourceSuffix, hc', Trace.target, List.append_assoc,
        List.singleton_append] using hybrid_after trace c.val
    rw [hbefore, hafter, oneEditTarget_insertion_split trace c bit hc,
      source_split_of_insertion trace c bit hc, hs, ht]
    exact common_suffix_change a b common (sourceSuffix trace c)
      (bit :: sourceSuffix trace c) L hL hcommon g
end DeletionCode.TraceSpectrumAssembly
