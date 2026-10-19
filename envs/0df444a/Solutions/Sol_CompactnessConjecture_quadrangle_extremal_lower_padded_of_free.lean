-- Prove2me | solution 1 for CompactnessConjecture.quadrangle_extremal_lower_padded_of_free
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/96c2a8fb-ff88-4cfc-9312-d5d48b097cc6

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_extremalNumber_monotone_of_no_isolated
import Theorems.Thm_CompactnessConjecture_quadrangle_extremal_lower_of_free

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    (K : Type*) [Field K] [Finite K]
    {U : Type*} (forbidden : SimpleGraph U)
    (hneighbors : ∀ u : U, ∃ v : U, forbidden.Adj u v)
    (hfree : forbidden.Free (symplecticQuadrangle K))
    {n : ℕ} (hn : quadrangleVertexCount (Nat.card K) ≤ n) :
    quadrangleEdgeCount (Nat.card K) ≤
      SimpleGraph.extremalNumber n forbidden := by
  exact (quadrangle_extremal_lower_of_free K forbidden hfree).trans
    (extremalNumber_monotone_of_no_isolated forbidden hneighbors hn)
end CompactnessConjecture
