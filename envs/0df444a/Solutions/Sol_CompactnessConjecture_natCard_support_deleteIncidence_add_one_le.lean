-- Prove2me | solution 1 for CompactnessConjecture.natCard_support_deleteIncidence_add_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/3c26310d-7356-45fc-b2d9-b7de8511269c

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace CompactnessConjecture
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {v : V} (hv : v ∈ G.support) :
    Nat.card (G.deleteIncidenceSet v).support + 1 ≤
      Nat.card G.support := by
  have hdrop := SimpleGraph.card_support_deleteIncidenceSet G hv
  have hpositive : 0 < Nat.card G.support :=
    Finite.card_pos_iff.mpr ⟨⟨v, hv⟩⟩
  simp only [Nat.card_eq_fintype_card] at hpositive ⊢
  omega
end CompactnessConjecture
