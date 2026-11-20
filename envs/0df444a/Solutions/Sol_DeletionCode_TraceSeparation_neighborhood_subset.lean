-- Prove2me | solution 1 for DeletionCode.TraceSeparation.neighborhood_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:43:58.474022+00:00
-- url     : https://prove2.me/submissions/f7f7db3d-188e-4b6b-a459-9875a957897b

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
import Theorems.Thm_DeletionCode_TraceSeparation_neighborhood_bounds

set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph
namespace DeletionCode.TraceSeparation
theorem _root_.solution {L position n : ℕ} (hL : 1 ≤ L)
    (hmargins : 4 * L ≤ position ∧ position + 4 * L ≤ n) :
    neighborhood L position ⊆ Set.Ico 0 n := by
  have hbound := (neighborhood_bounds hL hmargins).2
  intro r hr
  exact ⟨Nat.zero_le r, lt_of_lt_of_le hr.2 hbound⟩
end DeletionCode.TraceSeparation
