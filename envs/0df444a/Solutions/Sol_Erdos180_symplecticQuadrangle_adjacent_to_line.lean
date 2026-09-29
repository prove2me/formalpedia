-- Prove2me | solution 1 for Erdos180.symplecticQuadrangle_adjacent_to_line
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:35:58.597266+00:00
-- url     : https://prove2.me/submissions/f50bb8c8-a4cb-47c2-b5c1-6660f7454aae

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem solution
    {L : SymplecticLine K} {v : QuadrangleVertex K}
    (h : (symplecticQuadrangle K).Adj (.inr L) v) :
    ∃ p : SymplecticPoint K, v = .inl p ∧ p.1 ≤ L.1 := by
  rcases v with p | M
  · exact ⟨p, rfl,
      (symplecticQuadrangle_incidence_adj K p L).mp h.symm⟩
  · simp [symplecticQuadrangle, SimpleGraph.fromRel_adj,
      quadrangleIncidence] at h
