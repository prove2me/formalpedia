-- Prove2me | solution 1 for DeletionCode.TraceSeparation.neighborhood_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:36:52.393735+00:00
-- url     : https://prove2.me/submissions/27fd7672-97e8-4bfd-b7ec-b7fcad6f7cca

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation

set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph
namespace DeletionCode.TraceSeparation
theorem _root_.solution {L position n : ℕ} (hL : 1 ≤ L)
    (hmargins : 4 * L ≤ position ∧ position + 4 * L ≤ n) :
    neighborhoodLeft L position + 2 * L = neighborhoodRight L position ∧
      neighborhoodRight L position ≤ n := by
  unfold neighborhoodLeft neighborhoodRight
  constructor <;> omega
end DeletionCode.TraceSeparation
