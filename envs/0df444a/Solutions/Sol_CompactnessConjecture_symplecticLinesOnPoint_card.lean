-- Prove2me | solution 1 for CompactnessConjecture.symplecticLinesOnPoint_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/57dd3709-1d80-432a-b065-ea7f5faf75a8

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticPointQuotient_finrank

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution [Finite K]
    (p : SymplecticPoint K) :
    Nat.card (SymplecticLinesOnPoint K p) = Nat.card K + 1 := by
  rw [Nat.card_congr (symplecticLinesOnPointEquiv K p)]
  exact Projectivization.card_of_finrank_two K
    (SymplecticPointQuotient K p)
    (symplecticPointQuotient_finrank K p)
end CompactnessConjecture
