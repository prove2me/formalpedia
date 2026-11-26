-- Prove2me | solution 1 for Erdos1007.Standalone.Mathlib.InlineErdos1007.degree_ge_three_of_hasDimension_four_nine_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:56:42.727538+00:00
-- url     : https://prove2.me/submissions/78016334-453d-4a20-b8bd-3dbc1add8cb2

module
public import Definitions.Def_Erdos1007_Standalone_Mathlib_InlineErdos1007
public import Definitions.Def_Erdos1007_Combinatorics_SimpleGraph_FiveVertices
public import Definitions.Def_Erdos1007_Combinatorics_SimpleGraph_NineEdges
public import Definitions.Def_Erdos1007_Combinatorics_SimpleGraph_SixVertices
public import Definitions.Def_Erdos1007_Geometry_CompleteBipartite
public import Definitions.Def_Erdos1007_Geometry_CompleteBipartiteLowerBound
public import Definitions.Def_Erdos1007_Geometry_CompleteMinusEdge
public import Definitions.Def_Erdos1007_Geometry_FinLe
public import Definitions.Def_Erdos1007_Geometry_LowDegree
public import Definitions.Def_Erdos1007_Geometry_Prism
public import Definitions.Def_Erdos1007_Geometry_UnitDistanceComap
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Logic.Basic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Bounds.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Definitions.Def_Erdos1007_Standalone_Mathlib_InlineErdos1007Proof
public import Theorems.Thm_Erdos1007_Standalone_Mathlib_InlineErdos1007_not_unitDistance_le_three_of_hasDimension_four
public import Theorems.Thm_Erdos1007_unitDistance_of_nine_edges_degree_le_two


set_option autoImplicit false
@[expose] public section
public section
open Erdos1007 Erdos1007.Standalone Erdos1007.Standalone.Mathlib Erdos1007.Standalone.Mathlib.InlineErdos1007
open SimpleGraph
namespace Erdos1007.Standalone.Mathlib.InlineErdos1007
theorem _root_.solution
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdim : HasDimension G 4) (hEdges : G.edgeSet.ncard = 9)
    (hnbr : ∀ v : V, ∃ w : V, G.Adj v w) : ∀ v, 3 ≤ G.degree v := by
  have hcard : G.edgeFinset.card = 9 :=
    (Set.ncard_eq_toFinset_card' G.edgeSet).symm.trans hEdges
  intro v
  have hpos : 0 < G.degree v := (G.degree_pos_iff_exists_adj v).mpr (hnbr v)
  rcases Nat.lt_or_ge (G.degree v) 3 with hlt | hge
  · have hle : G.degree v ≤ 2 := Nat.lt_succ_iff.mp hlt
    exact False.elim (not_unitDistance_le_three_of_hasDimension_four hdim le_rfl
      (unitDistance_of_nine_edges_degree_le_two hcard hle hpos))
  · exact hge
end Erdos1007.Standalone.Mathlib.InlineErdos1007
