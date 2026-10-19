-- Prove2me | solution 1 for CompactnessConjecture.edgeFinset_card_eq_natCard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/205bad26-eecd-4207-b9ab-3238d98694be

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace CompactnessConjecture
theorem _root_.solution {V : Type*} (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    G.edgeFinset.card = Nat.card G.edgeSet := by
  simpa only [Nat.card_eq_fintype_card] using
    (SimpleGraph.edgeFinset_card (G := G))
end CompactnessConjecture
