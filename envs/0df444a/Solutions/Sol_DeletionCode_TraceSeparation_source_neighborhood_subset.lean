-- Prove2me | solution 1 for DeletionCode.TraceSeparation.source_neighborhood_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:47:37.151743+00:00
-- url     : https://prove2.me/submissions/fd5eb0e9-3c63-4a4d-b41d-c4ca9413bb97

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
import Theorems.Thm_DeletionCode_TraceSeparation_sourcePosition_margins
import Theorems.Thm_DeletionCode_TraceSeparation_neighborhood_subset

set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph
namespace DeletionCode.TraceSeparation
theorem _root_.solution {trace : Trace} {L : ℕ} (hL : 1 ≤ L)
    (hsep : Separated (4 * L) trace) (i : Fin trace.length) (hi : EditIndex trace i) :
    neighborhood L (trace.sourcePosition i.val) ⊆ Set.Ico 0 trace.source.length :=
  neighborhood_subset hL (sourcePosition_margins hsep i hi)
end DeletionCode.TraceSeparation
