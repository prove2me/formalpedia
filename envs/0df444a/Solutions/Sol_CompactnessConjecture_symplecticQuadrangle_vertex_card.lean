-- Prove2me | solution 1 for CompactnessConjecture.symplecticQuadrangle_vertex_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/96e9f02f-7dc2-4eae-af38-58ec7b6f165a

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticPoint_card
import Theorems.Thm_CompactnessConjecture_symplecticLine_card

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution [Finite K] :
    Nat.card (QuadrangleVertex K) =
      2 * (Nat.card K + 1) * ((Nat.card K) ^ 2 + 1) := by
  rw [Nat.card_sum, symplecticPoint_card, symplecticLine_card]
  ring
end CompactnessConjecture
