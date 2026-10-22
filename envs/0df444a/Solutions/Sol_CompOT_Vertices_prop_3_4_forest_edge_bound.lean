-- Prove2me | solution 1 for CompOT.Vertices.prop_3_4_forest_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:01:59.910957+00:00
-- url     : https://prove2.me/submissions/b7927710-890d-48c5-b7a9-2fde5760c075

import Mathlib
set_option autoImplicit false

theorem solution {V : Type*} [Finite V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) :
    Nat.card G.edgeSet ≤ Nat.card V - 1 := by
  classical
  have := Fintype.ofFinite V
  rcases isEmpty_or_nonempty V with hV | hV
  · have : IsEmpty G.edgeSet := ⟨fun e => by
      obtain ⟨e, he⟩ := e
      induction e using Sym2.ind with
      | _ a b => exact hV.false a⟩
    simp
  · have hconn : (⊤ : SimpleGraph V).Connected := SimpleGraph.connected_top
    obtain ⟨F, hGF, -, hF⟩ := hconn.exists_isTree_le_of_le_of_isAcyclic le_top hG
    have h1 := hF.card_edgeFinset
    have h2 : G.edgeFinset.card ≤ F.edgeFinset.card :=
      Finset.card_le_card (SimpleGraph.edgeFinset_mono hGF)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    omega
