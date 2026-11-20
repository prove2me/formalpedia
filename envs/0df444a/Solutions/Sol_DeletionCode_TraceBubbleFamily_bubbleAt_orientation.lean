-- Prove2me | solution 1 for DeletionCode.TraceBubbleFamily.bubbleAt_orientation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:57:14.991928+00:00
-- url     : https://prove2.me/submissions/f2d97e40-12cf-494d-aa9a-479a18a038b3

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_RunBubbleConstruction
import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_TraceBubbleFamily

set_option autoImplicit true
open DeletionCode DeletionCode.TraceBubbleFamily
open Windows HeaderRecovery CatalogueWords AlignmentTrace FiniteConflictGraph
open RunBubbleConstruction TraceEditData
namespace DeletionCode.TraceBubbleFamily
theorem _root_.solution (trace : Trace) (k : ℕ)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace) (c : EditColumn trace) :
    (bubbleAt trace k hx hsep c).bubble.orientation = orientation trace c :=
  (bubbleAt trace k hx hsep c).orientation_eq
end DeletionCode.TraceBubbleFamily
