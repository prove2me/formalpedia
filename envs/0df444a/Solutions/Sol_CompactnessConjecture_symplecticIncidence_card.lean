-- Prove2me | solution 1 for CompactnessConjecture.symplecticIncidence_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/ac93710c-c898-4860-b2ac-1cb63f71f7e5

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticPoint_card
import Theorems.Thm_CompactnessConjecture_symplecticIncidence_card_by_points

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution [Finite K] :
    Nat.card (SymplecticIncidence K) =
      (Nat.card K + 1) ^ 2 * ((Nat.card K) ^ 2 + 1) := by
  rw [symplecticIncidence_card_by_points, symplecticPoint_card]
  ring
end CompactnessConjecture
