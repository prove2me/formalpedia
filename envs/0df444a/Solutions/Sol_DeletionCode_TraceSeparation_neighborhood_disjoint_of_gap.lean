-- Prove2me | solution 1 for DeletionCode.TraceSeparation.neighborhood_disjoint_of_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:43:55.194603+00:00
-- url     : https://prove2.me/submissions/91e9d59e-5b1c-4866-bf05-d34b791140c0

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
import Theorems.Thm_DeletionCode_TraceSeparation_neighborhood_ordered

set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph
namespace DeletionCode.TraceSeparation
theorem _root_.solution {L a b : ℕ} (hL : 1 ≤ L)
    (hgap : a + 4 * L ≤ b) : Disjoint (neighborhood L a) (neighborhood L b) := by
  have horder := neighborhood_ordered hL hgap
  apply Set.disjoint_left.mpr
  intro r ha hb
  have hra := ha.2
  have hrb := hb.1
  omega
end DeletionCode.TraceSeparation
