-- Prove2me | solution 1 for CompactnessConjecture.symplecticIncidence_card_by_lines
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/a5a43872-b9da-47a5-a93e-86345c36ea8f

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticPointsOnLine_card

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution [Finite K] :
    Nat.card (SymplecticIncidence K) =
      Nat.card (SymplecticLine K) * (Nat.card K + 1) := by
  classical
  letI : Fintype (SymplecticPoint K) := Fintype.ofFinite _
  letI : Fintype (SymplecticLine K) := Fintype.ofFinite _
  calc
    Nat.card (SymplecticIncidence K) =
        Nat.card (Σ L : SymplecticLine K,
          SymplecticPointsOnLine K L) :=
      Nat.card_congr (symplecticIncidenceEquivSigmaLines K)
    _ = ∑ L : SymplecticLine K,
          Nat.card (SymplecticPointsOnLine K L) := by
      simp_rw [Nat.card_eq_fintype_card]
      exact Fintype.card_sigma
    _ = Nat.card (SymplecticLine K) * (Nat.card K + 1) := by
      simp_rw [symplecticPointsOnLine_card]
      simp [Nat.card_eq_fintype_card]
end CompactnessConjecture
