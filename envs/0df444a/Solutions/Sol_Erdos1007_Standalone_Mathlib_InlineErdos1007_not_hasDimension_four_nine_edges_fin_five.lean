-- Prove2me | solution 1 for Erdos1007.Standalone.Mathlib.InlineErdos1007.not_hasDimension_four_nine_edges_fin_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:55:31.938193+00:00
-- url     : https://prove2.me/submissions/7585a842-985e-4e54-a0b6-bd2e35201e0a

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
public import Theorems.Thm_Erdos1007_completeGraph_five_deleteEdge_unitDistance
public import Theorems.Thm_Erdos1007_nine_edges_iso_deleteEdge
public import Theorems.Thm_Erdos1007_unitDistance_of_embedding


set_option autoImplicit false
@[expose] public section
public section
open Erdos1007 Erdos1007.Standalone Erdos1007.Standalone.Mathlib Erdos1007.Standalone.Mathlib.InlineErdos1007
open SimpleGraph
namespace Erdos1007.Standalone.Mathlib.InlineErdos1007
theorem _root_.solution
    {G : SimpleGraph (Fin 5)}
    (hdim : HasDimension G 4) (hEdges : G.edgeSet.ncard = 9) : False := by
  classical
  have hcard : G.edgeFinset.card = 9 :=
    (Set.ncard_eq_toFinset_card' G.edgeSet).symm.trans hEdges
  obtain ⟨a, b, hab, ⟨φ⟩⟩ := nine_edges_iso_deleteEdge hcard
  obtain ⟨e, hea, heb⟩ : ∃ e : Fin 5 ≃ Fin 5, e a = 3 ∧ e b = 4 := by
    let e1 : Fin 5 ≃ Fin 5 := Equiv.setValue (Equiv.refl (Fin 5)) a 3
    have he1 : e1 a = 3 := Equiv.setValue_eq (Equiv.refl (Fin 5)) a 3
    have hsym : a ≠ e1.symm (4 : Fin 5) := by
      intro hps
      have : e1 a = 4 := by
        rw [hps]
        exact e1.apply_symm_apply 4
      rw [he1] at this
      exact absurd this (by decide : (3 : Fin 5) ≠ 4)
    have hea' : Equiv.setValue e1 b 4 a = 3 := by
      unfold Equiv.setValue
      rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hab hsym]
      exact he1
    exact ⟨Equiv.setValue e1 b 4, hea', Equiv.setValue_eq e1 b 4⟩
  let ψ : (⊤ : SimpleGraph (Fin 5)).deleteEdges {s(a, b)} ≃g
      (⊤ : SimpleGraph (Fin 5)).deleteEdges {s(3, 4)} :=
    { __ := e
      map_rel_iff' := by
        intro u v
        simp only [deleteEdges_adj, top_adj, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hne, hnot⟩
          constructor
          · exact e.injective.ne_iff.mp hne
          · intro hs
            apply hnot
            rcases (Sym2.eq_iff).mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · rw [hea, heb]
            · rw [heb, hea]
              exact Sym2.eq_swap
        · rintro ⟨hne, hnot⟩
          constructor
          · exact e.injective.ne hne
          · intro hs
            apply hnot
            rcases (Sym2.eq_iff).mp hs with ⟨hu, hv⟩ | ⟨hu, hv⟩
            · have hu' : u = a := e.injective (hu.trans hea.symm)
              have hv' : v = b := e.injective (hv.trans heb.symm)
              rw [hu', hv']
            · have hu' : u = b := e.injective (hu.trans heb.symm)
              have hv' : v = a := e.injective (hv.trans hea.symm)
              rw [hu', hv']
              exact Sym2.eq_swap }
  exact not_unitDistance_le_three_of_hasDimension_four hdim le_rfl
    (unitDistance_of_embedding (Iso.comp ψ φ).toEmbedding
      completeGraph_five_deleteEdge_unitDistance)
end Erdos1007.Standalone.Mathlib.InlineErdos1007
