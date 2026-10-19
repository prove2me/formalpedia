-- Prove2me | solution 1 for CompactnessConjecture.quadrangle_extremal_lower_of_free
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/185d75df-4a2e-4ca0-a06e-b5788af4b615

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_vertex_card
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_edge_card

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    (K : Type*) [Field K] [Finite K]
    {U : Type*} (forbidden : SimpleGraph U)
    (hfree : forbidden.Free (symplecticQuadrangle K)) :
    quadrangleEdgeCount (Nat.card K) ≤
      SimpleGraph.extremalNumber
        (quadrangleVertexCount (Nat.card K)) forbidden := by
  classical
  letI : Fintype (QuadrangleVertex K) := Fintype.ofFinite _
  have hvertex : Fintype.card (QuadrangleVertex K) =
      quadrangleVertexCount (Nat.card K) := by
    rw [← Nat.card_eq_fintype_card, symplecticQuadrangle_vertex_card]
    rfl
  calc
    quadrangleEdgeCount (Nat.card K) =
        (symplecticQuadrangle K).edgeFinset.card := by
      rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
        symplecticQuadrangle_edge_card]
      rfl
    _ ≤ SimpleGraph.extremalNumber
          (Fintype.card (QuadrangleVertex K)) forbidden :=
      SimpleGraph.card_edgeFinset_le_extremalNumber hfree
    _ = SimpleGraph.extremalNumber
          (quadrangleVertexCount (Nat.card K)) forbidden := by
      rw [hvertex]
end CompactnessConjecture
