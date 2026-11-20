-- Prove2me | solution 1 for DeletionCode.TraceBubbleFamily.bubbleAt_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:57:37.11568+00:00
-- url     : https://prove2.me/submissions/53327794-96f3-4695-b5b5-959718180541

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
    oneEditTarget trace c = (bubbleAt trace k hx hsep c).before ++
      (bubbleAt trace k hx hsep c).bubble.positiveWord ++ (bubbleAt trace k hx hsep c).after :=
  (bubbleAt trace k hx hsep c).target_eq
end DeletionCode.TraceBubbleFamily
