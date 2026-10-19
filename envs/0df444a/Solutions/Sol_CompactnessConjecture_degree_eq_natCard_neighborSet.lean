-- Prove2me | solution 1 for CompactnessConjecture.degree_eq_natCard_neighborSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/d72f5273-ebd8-44d2-a336-3ba8f2524a9f

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace CompactnessConjecture
theorem _root_.solution {V : Type*}
    (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] :
    G.degree v = Nat.card (G.neighborSet v) := by
  simpa only [Nat.card_eq_fintype_card] using
    (SimpleGraph.card_neighborSet_eq_degree G v).symm
end CompactnessConjecture
