-- Prove2me | solution 1 for Conway99.conway_99_edgeFinset_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-06T16:52:14.948515+00:00
-- url     : https://prove2.me/submissions/8fb26586-572e-46e4-8b18-47089c69021f

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph Finset

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {g : SimpleGraph V} [DecidableRel g.Adj] (h : g.IsSRGWith 99 14 1 2) :
    g.edgeFinset.card = 693 := by
  classical
  have hsum : ∑ v : V, g.degree v = 2 * g.edgeFinset.card :=
    g.sum_degrees_eq_twice_card_edges
  have hd : ∑ v : V, g.degree v = 99 * 14 := by
    rw [Finset.sum_congr rfl (fun v _ => h.regular v), Finset.sum_const, Finset.card_univ,
      h.card, smul_eq_mul]
  omega
