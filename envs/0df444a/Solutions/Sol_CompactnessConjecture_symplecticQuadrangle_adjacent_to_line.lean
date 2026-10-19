-- Prove2me | solution 1 for CompactnessConjecture.symplecticQuadrangle_adjacent_to_line
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/3d835f79-0886-4243-91ec-dc9c30eea569

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    {L : SymplecticLine K} {v : QuadrangleVertex K}
    (h : (symplecticQuadrangle K).Adj (.inr L) v) :
    ∃ p : SymplecticPoint K, v = .inl p ∧ p.1 ≤ L.1 := by
  rcases v with p | M
  · exact ⟨p, rfl,
      (symplecticQuadrangle_incidence_adj K p L).mp h.symm⟩
  · simp [symplecticQuadrangle, SimpleGraph.fromRel_adj,
      quadrangleIncidence] at h
end CompactnessConjecture
