-- Prove2me | solution 1 for Erdos180.encodeFiniteGraph_not_acyclic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:38:54.690099+00:00
-- url     : https://prove2.me/submissions/20e6a0da-484c-4b9b-9a31-353e33e5ae88

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Erdos180
open Finset SimpleGraph

theorem solution
    {α : Type*} [Fintype α]
    (graph : SimpleGraph α) (h : ¬ graph.IsAcyclic) :
    ¬ (encodeFiniteGraph graph).graph.IsAcyclic := by
  intro hencoded
  apply h
  exact (SimpleGraph.Iso.map (Fintype.equivFin α) graph).isAcyclic_iff.mpr
    hencoded
