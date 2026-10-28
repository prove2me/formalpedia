-- Prove2me | solution 1 for FiniteGraph.edgeSet_ne_of_new_reachable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:25:40.490154+00:00
-- url     : https://prove2.me/submissions/6cd1746f-6f51-425c-be3d-59663c6ff162

import Mathlib
theorem solution
    {V : Type} [Fintype V]
    (F H : SimpleGraph V)
    (hnew : ∃ u v : V, ¬ F.Reachable u v ∧ H.Reachable u v) :
    H.edgeSet ≠ F.edgeSet := by
  intro h
  obtain ⟨u, v, hF, hH⟩ := hnew
  have : H = F := SimpleGraph.edgeSet_injective h
  exact hF (this ▸ hH)
