-- Prove2me | solution 1 for DeletionCode.TraceBubbleFamily.bubbleAt_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:57:36.614539+00:00
-- url     : https://prove2.me/submissions/9b11d986-80cd-49a2-a581-bb5d65ec90b9

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
    trace.source = (bubbleAt trace k hx hsep c).before ++
      (bubbleAt trace k hx hsep c).bubble.negativeWord ++ (bubbleAt trace k hx hsep c).after :=
  (bubbleAt trace k hx hsep c).source_eq
end DeletionCode.TraceBubbleFamily
