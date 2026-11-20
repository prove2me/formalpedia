-- Prove2me | solution 1 for DeletionCode.LocalBubbleDisjoint.localVertex_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:49:44.487144+00:00
-- url     : https://prove2.me/submissions/1f532eb1-de49-44f7-9999-b8d3c3f5085c

import Definitions.Def_DeletionCode_SingleEditBubbles
import Definitions.Def_DeletionCode_EditLocality
import Definitions.Def_DeletionCode_LocalBubbleDisjoint
import Theorems.Thm_DeletionCode_LocalBubbleDisjoint_canonical_length
import Theorems.Thm_DeletionCode_LocalBubbleDisjoint_canonical_word
import Theorems.Thm_DeletionCode_SpectrumLocalization_listLetters_middle


set_option autoImplicit true
open DeletionCode DeletionCode.LocalBubbleDisjoint
open Windows HeaderRecovery CatalogueWords RunBubbleConstruction
open SingleEditOrigins BubbleContextGeometry SpectrumLocalization
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}
namespace DeletionCode.LocalBubbleDisjoint
theorem _root_.solution (p : LocalBubble k source target pos orientation) (side : Bool)
    (offset : ℕ) (hbound : offset + (windowLength k - 1) ≤ (pathWord p side).length) :
    localVertex p side offset ∈ EditLocality.localVertices (canonicalEdit p side)
      (listLetters source) p.before.length p.bubble.negativeWord.length (windowLength k) := by
  refine ⟨p.before.length + offset, by omega, ?_, ?_⟩
  · have hlength := canonical_length p side
    omega
  · funext i
    change (canonicalEdit p side).word (listLetters source)
      (p.before.length + offset + i.val) = listLetters (pathWord p side) (offset + i.val)
    rw [canonical_word]
    rw [show p.before.length + offset + i.val = p.before.length + (offset + i.val) by omega]
    exact listLetters_middle p.before (pathWord p side) p.after (offset + i.val)
      (by have hi := i.isLt; omega)
end DeletionCode.LocalBubbleDisjoint
