-- Prove2me | solution 1 for CompactnessConjecture.natCard_support_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/f790b418-94a3-4122-b661-5ab8d70b26d9

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace CompactnessConjecture
theorem _root_.solution
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Nat.card G.support ≤ Fintype.card V := by
  simpa only [Nat.card_eq_fintype_card] using
    (Finite.card_subtype_le (fun v : V => v ∈ G.support))
end CompactnessConjecture
