-- Prove2me | solution 1 for CompactnessConjecture.encodeFiniteGraph_not_acyclic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/fcc0837a-8f50-4da2-a891-49d8095f53ee

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {α : Type*} [Fintype α]
    (graph : SimpleGraph α) (h : ¬ graph.IsAcyclic) :
    ¬ (encodeFiniteGraph graph).graph.IsAcyclic := by
  intro hencoded
  apply h
  exact (SimpleGraph.Iso.map (Fintype.equivFin α) graph).isAcyclic_iff.mpr
    hencoded
end CompactnessConjecture
