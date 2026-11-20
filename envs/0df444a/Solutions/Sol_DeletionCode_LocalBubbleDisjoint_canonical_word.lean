-- Prove2me | solution 1 for DeletionCode.LocalBubbleDisjoint.canonical_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:45:27.918214+00:00
-- url     : https://prove2.me/submissions/ff94f12b-8f10-4a67-9661-02410f2ebd41

import Definitions.Def_DeletionCode_SingleEditBubbles
import Definitions.Def_DeletionCode_EditLocality
import Definitions.Def_DeletionCode_LocalBubbleDisjoint
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_end
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_zero
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_BubbleContextGeometry_delete_context
import Theorems.Thm_DeletionCode_BubbleContextGeometry_insert_context
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
open DeletionCode DeletionCode.LocalBubbleDisjoint
open Windows HeaderRecovery CatalogueWords RunBubbleConstruction
open SingleEditOrigins BubbleContextGeometry SpectrumLocalization
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}
namespace DeletionCode.LocalBubbleDisjoint
theorem _root_.solution (p : LocalBubble k source target pos orientation) (side : Bool) :
    (canonicalEdit p side).word (listLetters source) =
      listLetters (p.before ++ (pathWord p side ++ p.after)) := by
  have hsource : source = p.before ++ (p.bubble.negativeWord ++ p.after) := by
    simpa only [List.append_assoc] using p.source_eq
  calc
    _ = (canonicalEdit p side).word
        (listLetters (p.before ++ (p.bubble.negativeWord ++ p.after))) :=
      congrArg (fun word : List Bool => (canonicalEdit p side).word (listLetters word)) hsource
    _ = _ := by
      cases side with
      | false => rfl
      | true =>
        cases ho : p.bubble.orientation with
        | deletion =>
          simpa only [pathWord, ite_true, canonicalEdit, ho,
            BubbleWord.negativeWord, BubbleWord.positiveWord, Edit.word] using
            delete_context p.bubble p.before p.after
        | insertion =>
          simpa only [pathWord, ite_true, canonicalEdit, ho,
            BubbleWord.negativeWord, BubbleWord.positiveWord, Edit.word] using
            insert_context p.bubble p.before p.after
end DeletionCode.LocalBubbleDisjoint
