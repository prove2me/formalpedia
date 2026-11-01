-- Prove2me | solution 1 for CombOpt.ShortestPath.prop_2_9
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:03:49.895075+00:00
-- url     : https://prove2.me/submissions/6de898e0-5799-4f97-a022-65642fd163eb

import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_CombOpt_ShortestPath_Digraph_IsFeasiblePotential
import Definitions.Def_CombOpt_ShortestPath_Digraph_IsDipath
import Definitions.Def_CombOpt_ShortestPath_pathCost

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open CombOpt.ShortestPath

theorem solution {V E : Type*} [Fintype V] [Fintype E] (G : Digraph V E) (c : E → ℝ) (r : V)
    (y : V → ℝ) (hy : G.IsFeasiblePotential c r y) (v : V) (P : List E)
    (hP : G.IsDipath r P v) :
    y v ≤ pathCost c P := by
  obtain ⟨hpot, hr⟩ := hy
  have hbound {u v : V} {L : List E} (hL : G.IsDipath u L v) :
      y v ≤ y u + pathCost c L := by
    induction hL with
    | nil u =>
        simp [pathCost]
    | @cons u v e L he htail ih =>
        have hedge := hpot e
        rw [he] at hedge
        have hcost : pathCost c (e :: L) = c e + pathCost c L := by
          simp [pathCost]
        rw [hcost]
        linarith
  simpa [hr] using hbound hP
