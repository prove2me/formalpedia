-- Prove2me | solution 1 for CompactnessConjecture.symplecticPoint_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/077c029d-5a13-462b-983c-084d84036d57

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution [Finite K] :
    Nat.card (SymplecticPoint K) =
      (Nat.card K + 1) * ((Nat.card K) ^ 2 + 1) := by
  calc
    Nat.card (SymplecticPoint K) =
        Nat.card (Projectivization K (SymplecticVector K)) :=
      Nat.card_congr
        (Projectivization.equivSubmodule K (SymplecticVector K)).symm
    _ = ∑ i ∈ Finset.range 4, (Nat.card K) ^ i :=
      Projectivization.card_of_finrank K (SymplecticVector K) (by simp)
    _ = (Nat.card K + 1) * ((Nat.card K) ^ 2 + 1) := by
      simp [Finset.sum_range_succ]
      ring
end CompactnessConjecture
