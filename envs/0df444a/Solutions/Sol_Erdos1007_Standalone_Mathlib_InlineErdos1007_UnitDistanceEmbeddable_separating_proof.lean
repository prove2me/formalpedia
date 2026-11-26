-- Prove2me | solution 1 for Erdos1007.Standalone.Mathlib.InlineErdos1007.UnitDistanceEmbeddable.separating.proof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:55:26.389099+00:00
-- url     : https://prove2.me/submissions/a6cbb209-8a8b-461d-9b5e-18e131a89815

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

set_option autoImplicit false
@[expose] public section
public section
open Erdos1007 Erdos1007.Standalone Erdos1007.Standalone.Mathlib Erdos1007.Standalone.Mathlib.InlineErdos1007
open SimpleGraph
namespace Erdos1007.Standalone.Mathlib.InlineErdos1007
namespace UnitDistanceEmbeddable.separating
theorem _root_.solution : UnitDistanceEmbeddable.separating := by
  have dist_axis {n : ℕ} (i : Fin n) (a b : ℝ) :
      dist (EuclideanSpace.single i a) (EuclideanSpace.single i b) = |a - b| := by
    rw [PiLp.dist_single_same, Real.dist_eq]
  have inj : Function.Injective (fun j : Fin 3 =>
      EuclideanSpace.single (0 : Fin 1) (j : ℝ)) := by
    intro u v h
    have hcoord := congr_arg (fun p : EuclideanSpace ℝ (Fin 1) => p 0) h
    simp only [PiLp.single_eq_same] at hcoord
    exact Fin.ext (Nat.cast_inj.mp hcoord)
  let f : Fin 3 → EuclideanSpace ℝ (Fin 1) := fun j => EuclideanSpace.single 0 (j : ℝ)
  refine ⟨Fin 3, fromEdgeSet {s(0, 1)}, 1, f, ⟨f, inj, ?_⟩, inj, ?_, 1, 2, ?_, ?_, ?_⟩
  · intro u v huv
    rw [fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at huv
    rcases huv with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩
    · rw [dist_axis]
      norm_num
    · rw [dist_axis]
      norm_num
  · intro u v huv
    rw [fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at huv
    rcases huv with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩
    · rw [dist_axis]
      norm_num
    · rw [dist_axis]
      norm_num
  · decide
  · rw [fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff]
    decide
  · rw [dist_axis]
    norm_num
end UnitDistanceEmbeddable.separating
end Erdos1007.Standalone.Mathlib.InlineErdos1007
