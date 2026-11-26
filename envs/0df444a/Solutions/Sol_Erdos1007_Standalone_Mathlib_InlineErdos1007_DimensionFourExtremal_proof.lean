-- Prove2me | solution 1 for Erdos1007.Standalone.Mathlib.InlineErdos1007.DimensionFourExtremal.proof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:58:36.433018+00:00
-- url     : https://prove2.me/submissions/325ecc15-e985-45a5-af07-0b8e8d2a572d

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
public import Theorems.Thm_Erdos1007_Standalone_Mathlib_InlineErdos1007_degree_ge_three_of_hasDimension_four_nine_edges
public import Theorems.Thm_Erdos1007_Standalone_Mathlib_InlineErdos1007_not_hasDimension_four_nine_edges_fin_five
public import Theorems.Thm_Erdos1007_Standalone_Mathlib_InlineErdos1007_iso_completeBipartiteGraph_three_three_of_hasDimension_four_fin_six
public import Theorems.Thm_Erdos1007_nine_edges_card_ge_five
public import Theorems.Thm_Erdos1007_nine_edges_minDegree_three_card_le_six


set_option autoImplicit false
@[expose] public section
public section
open Erdos1007 Erdos1007.Standalone Erdos1007.Standalone.Mathlib Erdos1007.Standalone.Mathlib.InlineErdos1007
open SimpleGraph
namespace Erdos1007.Standalone.Mathlib.InlineErdos1007
namespace DimensionFourExtremal
theorem _root_.solution : DimensionFourExtremal := by
  intro n G hdim hEdges hnbr
  let : DecidableRel G.Adj := Classical.decRel G.Adj
  have hcard : G.edgeFinset.card = 9 :=
    (Set.ncard_eq_toFinset_card' G.edgeSet).symm.trans hEdges
  have hmin : ∀ v, 3 ≤ G.degree v :=
    degree_ge_three_of_hasDimension_four_nine_edges hdim hEdges hnbr
  have hfive : 5 ≤ n := by
    simpa [Fintype.card_fin] using nine_edges_card_ge_five hcard
  have hsix : n ≤ 6 := by
    simpa [Fintype.card_fin] using nine_edges_minDegree_three_card_le_six hcard hmin
  have hn : n = 5 ∨ n = 6 := by omega
  rcases hn with rfl | rfl
  · exact False.elim (not_hasDimension_four_nine_edges_fin_five hdim hEdges)
  · exact iso_completeBipartiteGraph_three_three_of_hasDimension_four_fin_six
      hdim hEdges hnbr
end DimensionFourExtremal
end Erdos1007.Standalone.Mathlib.InlineErdos1007
