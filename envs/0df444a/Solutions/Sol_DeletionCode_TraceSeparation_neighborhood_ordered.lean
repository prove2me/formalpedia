-- Prove2me | solution 1 for DeletionCode.TraceSeparation.neighborhood_ordered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:36:50.545921+00:00
-- url     : https://prove2.me/submissions/a958a2ca-e518-4bcf-ba2d-9094bf787df1

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation

set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph
namespace DeletionCode.TraceSeparation
theorem _root_.solution {L a b : ℕ} (hL : 1 ≤ L)
    (hgap : a + 4 * L ≤ b) : neighborhoodRight L a ≤ neighborhoodLeft L b := by
  unfold neighborhoodLeft neighborhoodRight
  omega
end DeletionCode.TraceSeparation
