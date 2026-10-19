-- Prove2me | solution 1 for CompactnessConjecture.symplecticQuadrangle_edge_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/5cd53209-d596-470a-91e4-258897ca3e7b

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticIncidence_card

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution [Finite K] :
    Nat.card (symplecticQuadrangle K).edgeSet =
      (Nat.card K + 1) ^ 2 * ((Nat.card K) ^ 2 + 1) := by
  rw [← Nat.card_congr (symplecticIncidenceEquivEdge K),
    symplecticIncidence_card]
end CompactnessConjecture
