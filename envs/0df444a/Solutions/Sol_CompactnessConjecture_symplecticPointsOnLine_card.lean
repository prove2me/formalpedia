-- Prove2me | solution 1 for CompactnessConjecture.symplecticPointsOnLine_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/be2296b4-9cf3-4a99-8f8d-db5d974a81ef

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution [Finite K]
    (L : SymplecticLine K) :
    Nat.card (SymplecticPointsOnLine K L) = Nat.card K + 1 := by
  rw [Nat.card_congr (symplecticPointsOnLineEquiv K L)]
  exact Projectivization.card_of_finrank_two K L.1 L.2.1
end CompactnessConjecture
