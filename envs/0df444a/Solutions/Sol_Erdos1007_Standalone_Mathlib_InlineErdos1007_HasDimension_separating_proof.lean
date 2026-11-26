-- Prove2me | solution 1 for Erdos1007.Standalone.Mathlib.InlineErdos1007.HasDimension.separating.proof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:55:27.002951+00:00
-- url     : https://prove2.me/submissions/e32cea09-7ed9-4d76-8e6b-d5a63c5fe957

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
namespace HasDimension.separating
theorem _root_.solution : HasDimension.separating := by
  have dist_axis {n : ℕ} (i : Fin n) (a b : ℝ) :
      dist (EuclideanSpace.single i a) (EuclideanSpace.single i b) = |a - b| := by
    rw [PiLp.dist_single_same, Real.dist_eq]
  have k2 (n : ℕ) (i : Fin n) : UnitDistanceEmbeddable (completeGraph (Fin 2)) n := by
    refine ⟨fun j => EuclideanSpace.single i (j : ℝ), ?_, ?_⟩
    · intro u v h
      have hcoord := congr_arg (fun p : EuclideanSpace ℝ (Fin n) => p i) h
      simp only [PiLp.single_eq_same] at hcoord
      exact Fin.ext (Nat.cast_inj.mp hcoord)
    · intro u v huv
      fin_cases u <;> fin_cases v <;> rw [top_adj] at huv
      · exact (huv rfl).elim
      · rw [dist_axis]
        norm_num
      · rw [dist_axis]
        norm_num
      · exact (huv rfl).elim
  refine ⟨Fin 2, completeGraph (Fin 2), ⟨0, 1, ?_⟩, k2 4 0, ?_⟩
  · rw [top_adj]
    decide
  · intro h
    have hle : (4 : ℕ) ≤ 1 := (mem_lowerBounds.mp h.2) 1 (k2 1 0)
    exact absurd hle (by decide : ¬ (4 : ℕ) ≤ 1)
end HasDimension.separating
end Erdos1007.Standalone.Mathlib.InlineErdos1007
