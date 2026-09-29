-- Prove2me | solution 1 for FamousTheorems.tree_card_edges_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:01:31.440189+00:00
-- url     : https://prove2.me/submissions/4605b145-7ca3-40ae-a242-0cea56f5f727

import Mathlib

theorem solution {V : Type*} {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet] (hG : G.IsTree) :
    G.edgeFinset.card + 1 = Fintype.card V :=
  hG.card_edgeFinset
