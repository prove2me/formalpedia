-- Prove2me | solution 2 for ChromaticReconstruction.reachable_mono
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T11:42:47.466679+00:00
-- url     : https://prove2.me/submissions/293565a8-c3ef-40d6-8afc-90950a99233c

import Mathlib

open SimpleGraph

theorem solution {V : Type*} {A B : Set (Sym2 V)} (hAB : A ⊆ B) {u v : V}
    (huv : (SimpleGraph.fromEdgeSet A).Reachable u v) :
    (SimpleGraph.fromEdgeSet B).Reachable u v :=
  Reachable.mono (SimpleGraph.fromEdgeSet_mono hAB) huv
