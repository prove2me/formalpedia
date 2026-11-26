-- Prove2me | solution 1 for Erdos1007.Standalone.Mathlib.InlineErdos1007.hasDimension_completeBipartiteGraph_three_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:56:43.269628+00:00
-- url     : https://prove2.me/submissions/6132f8cc-b914-4515-8024-e9293d2307f7

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
public import Theorems.Thm_Erdos1007_completeBipartiteGraph_three_three_unitDistance
public import Theorems.Thm_Erdos1007_not_exists_completeBipartiteGraph_three_three_unitDistance_three
public import Theorems.Thm_Erdos1007_unitDistance_of_fin_le


set_option autoImplicit false
@[expose] public section
public section
open Erdos1007 Erdos1007.Standalone Erdos1007.Standalone.Mathlib Erdos1007.Standalone.Mathlib.InlineErdos1007
open SimpleGraph
namespace Erdos1007.Standalone.Mathlib.InlineErdos1007
theorem _root_.solution :
    HasDimension (completeBipartiteGraph (Fin 3) (Fin 3)) 4 := by
  refine ⟨?_, ?_⟩
  · obtain ⟨f, hfInj, hfDist⟩ := completeBipartiteGraph_three_three_unitDistance
    exact ⟨f, hfInj, hfDist⟩
  · rw [mem_lowerBounds]
    intro m hm
    have hmle : ¬ m ≤ 3 := fun hle =>
      not_exists_completeBipartiteGraph_three_three_unitDistance_three
        (unitDistance_of_fin_le hle hm)
    exact Nat.succ_le_of_lt (Nat.gt_of_not_le hmle)
end Erdos1007.Standalone.Mathlib.InlineErdos1007
