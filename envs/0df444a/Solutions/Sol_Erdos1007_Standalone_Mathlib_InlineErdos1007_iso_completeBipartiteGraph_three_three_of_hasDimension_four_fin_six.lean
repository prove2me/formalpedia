-- Prove2me | solution 1 for Erdos1007.Standalone.Mathlib.InlineErdos1007.iso_completeBipartiteGraph_three_three_of_hasDimension_four_fin_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:57:40.698831+00:00
-- url     : https://prove2.me/submissions/d27fb1e6-d166-4a99-a3ab-1c1fb4f6910d

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
public import Theorems.Thm_Erdos1007_Standalone_Mathlib_InlineErdos1007_degree_ge_three_of_hasDimension_four_nine_edges
public import Theorems.Thm_Erdos1007_compl_cycleGraph_six_unitDistance
public import Theorems.Thm_Erdos1007_nine_edges_six_minDegree_three
public import Theorems.Thm_Erdos1007_unitDistance_of_embedding


set_option autoImplicit false
@[expose] public section
public section
open Erdos1007 Erdos1007.Standalone Erdos1007.Standalone.Mathlib Erdos1007.Standalone.Mathlib.InlineErdos1007
open SimpleGraph
namespace Erdos1007.Standalone.Mathlib.InlineErdos1007
theorem _root_.solution
    {G : SimpleGraph (Fin 6)}
    (hdim : HasDimension G 4) (hEdges : G.edgeSet.ncard = 9)
    (hnbr : ∀ v : Fin 6, ∃ w : Fin 6, G.Adj v w) :
    Nonempty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := by
  classical
  have hcard : G.edgeFinset.card = 9 :=
    (Set.ncard_eq_toFinset_card' G.edgeSet).symm.trans hEdges
  have hmin : ∀ v, 3 ≤ G.degree v :=
    degree_ge_three_of_hasDimension_four_nine_edges hdim hEdges hnbr
  rcases nine_edges_six_minDegree_three hcard hmin with hK | hC
  · exact hK
  · obtain ⟨e⟩ := hC
    let ψ : G ≃g (cycleGraph 6)ᶜ :=
      { toEquiv := e.toEquiv
        map_rel_iff' := by
          intro u v
          simp only [RelIso.coe_fn_toEquiv]
          rw [compl_adj, e.map_adj_iff, (EquivLike.injective e).ne_iff]
          constructor
          · intro h
            rcases h with ⟨hne, hn⟩
            exact if hadj : G.Adj u v then hadj else
              absurd ((compl_adj G u v).mpr ⟨hne, hadj⟩) hn
          · intro hadj
            exact ⟨hadj.ne, fun hcompl => ((compl_adj G u v).mp hcompl).2 hadj⟩ }
    exact False.elim (not_unitDistance_le_three_of_hasDimension_four hdim
      (by decide : (2 : ℕ) ≤ 3)
      (unitDistance_of_embedding ψ.toEmbedding compl_cycleGraph_six_unitDistance))
end Erdos1007.Standalone.Mathlib.InlineErdos1007
