-- Prove2me | solution 1 for CompactnessConjecture.symplecticQuadrangle_adjacent_to_point
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/933e72d1-72bb-433f-bc31-deb9a6518513

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    {p : SymplecticPoint K} {v : QuadrangleVertex K}
    (h : (symplecticQuadrangle K).Adj (.inl p) v) :
    ∃ L : SymplecticLine K, v = .inr L ∧ p.1 ≤ L.1 := by
  rcases v with q | L
  · simp [symplecticQuadrangle, SimpleGraph.fromRel_adj,
      quadrangleIncidence] at h
  · exact ⟨L, rfl, (symplecticQuadrangle_incidence_adj K p L).mp h⟩
end CompactnessConjecture
