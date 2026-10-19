-- Prove2me | solution 1 for CompactnessConjecture.symplecticLine_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/594bb3b6-9b7f-42af-a1ff-3579d446cb17

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticPoint_card
import Theorems.Thm_CompactnessConjecture_symplecticIncidence_card_by_points
import Theorems.Thm_CompactnessConjecture_symplecticIncidence_card_by_lines

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution [Finite K] :
    Nat.card (SymplecticLine K) =
      (Nat.card K + 1) * ((Nat.card K) ^ 2 + 1) := by
  have hcounts :
      Nat.card (SymplecticPoint K) * (Nat.card K + 1) =
        Nat.card (SymplecticLine K) * (Nat.card K + 1) :=
    (symplecticIncidence_card_by_points K).symm.trans
      (symplecticIncidence_card_by_lines K)
  have hline : Nat.card (SymplecticPoint K) =
      Nat.card (SymplecticLine K) :=
    Nat.eq_of_mul_eq_mul_right (Nat.succ_pos _) hcounts
  rw [← hline, symplecticPoint_card]
end CompactnessConjecture
