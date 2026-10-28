-- Prove2me | solution 1 for Balinski61.Connectivity.disjoint_paths_between_vertices
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T07:46:26.990209+00:00
-- url     : https://prove2.me/submissions/d0c55e4e-9433-4392-8bc1-ea65b88b6e99

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Set.Card
import Definitions.Def_Hirsch_model
import Definitions.Def_Balinski61_Connectivity_Polyhedron
import Definitions.Def_Balinski61_Connectivity_TuplyConnected
import Definitions.Def_Balinski61_Whitney_Graph
import Theorems.Thm_Balinski61_Connectivity_graph_n_tuply_connected
import Theorems.Thm_Balinski61_Connectivity_convexHull_vertices_not_in_hyperplane
import Theorems.Thm_Balinski61_Whitney_whitney_theorem

open scoped RealInnerProductSpace
open Balinski61.Connectivity

theorem solution (n m : ℕ)
    (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hS : StandingAssumptions a b)
    (u v : Set.extremePoints ℝ (Hirsch.Hpoly a b)) (huv : u ≠ v) :
    HasDisjointPaths (polyGraph (Hirsch.Hpoly a b)) u v n := by
  have hfin : (Set.extremePoints ℝ (Hirsch.Hpoly a b)).Finite :=
    (convexHull_vertices_not_in_hyperplane n m a b hS).1
  haveI : Fintype (Set.extremePoints ℝ (Hirsch.Hpoly a b)) := hfin.fintype
  have hcard2 : 2 ≤ Fintype.card (Set.extremePoints ℝ (Hirsch.Hpoly a b)) :=
    Fintype.one_lt_card_iff.mpr ⟨u, v, huv⟩
  obtain ⟨hcard, hconn⟩ := graph_n_tuply_connected n m a b hS
  have hW : Balinski61.Whitney.IsNTuplyConnected (polyGraph (Hirsch.Hpoly a b)) n := by
    refine ⟨?_, fun X hX => ?_⟩
    · rw [Set.encard_univ, ENat.card_eq_coe_fintype_card] at hcard
      exact_mod_cast hcard
    · apply hconn (X : Set (Set.extremePoints ℝ (Hirsch.Hpoly a b)))
      rw [Set.encard_coe_eq_coe_finsetCard]
      exact_mod_cast hX
  exact (Balinski61.Whitney.whitney_theorem (polyGraph (Hirsch.Hpoly a b)) n hcard2).mp hW u v huv
