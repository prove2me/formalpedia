-- Prove2me | solution 1 for DeletionCode.TraceBubbleFamily.indexedBubbleWords_orientation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:58:37.463433+00:00
-- url     : https://prove2.me/submissions/285455ca-95cf-44fa-88b1-1fc399f2d0fa

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_RunBubbleConstruction
import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_TraceBubbleFamily
import Theorems.Thm_DeletionCode_TraceBubbleFamily_bubbleAt_orientation

set_option autoImplicit true
open DeletionCode DeletionCode.TraceBubbleFamily
open Windows HeaderRecovery CatalogueWords AlignmentTrace FiniteConflictGraph
open RunBubbleConstruction TraceEditData
namespace DeletionCode.TraceBubbleFamily
theorem _root_.solution (trace : Trace) (k t : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace)
    (hdel : trace.deletions = t) (hins : trace.insertions = t) (i : Fin (2 * t)) :
    (indexedBubbleWords trace k t hx hsep hdel hins i).orientation =
      orientation trace (editEquiv trace t hdel hins i) :=
  bubbleAt_orientation trace k hx hsep (editEquiv trace t hdel hins i)
end DeletionCode.TraceBubbleFamily
