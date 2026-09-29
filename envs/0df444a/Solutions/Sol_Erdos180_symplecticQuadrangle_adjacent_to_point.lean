-- Prove2me | solution 1 for Erdos180.symplecticQuadrangle_adjacent_to_point
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:35:17.218977+00:00
-- url     : https://prove2.me/submissions/371a2962-4db2-4ebb-8077-5bbd17037107

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem solution
    {p : SymplecticPoint K} {v : QuadrangleVertex K}
    (h : (symplecticQuadrangle K).Adj (.inl p) v) :
    ∃ L : SymplecticLine K, v = .inr L ∧ p.1 ≤ L.1 := by
  rcases v with q | L
  · simp [symplecticQuadrangle, SimpleGraph.fromRel_adj,
      quadrangleIncidence] at h
  · exact ⟨L, rfl, (symplecticQuadrangle_incidence_adj K p L).mp h⟩
