-- Prove2me | solution 1 for Erdos1007.Standalone.Mathlib.InlineErdos1007.DimensionFourExtremal.witness.proof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:57:29.03908+00:00
-- url     : https://prove2.me/submissions/1da4e89b-fb3c-4435-ac6b-2fdf61891ff5

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
public import Theorems.Thm_Erdos1007_Standalone_Mathlib_InlineErdos1007_hasDimension_completeBipartiteGraph_three_three

set_option autoImplicit false
@[expose] public section
public section
open Erdos1007 Erdos1007.Standalone Erdos1007.Standalone.Mathlib Erdos1007.Standalone.Mathlib.InlineErdos1007
open SimpleGraph
namespace Erdos1007.Standalone.Mathlib.InlineErdos1007
namespace DimensionFourExtremal.witness
theorem _root_.solution : DimensionFourExtremal.witness := by
  -- `K₃,₃` on `Fin 3 ⊕ Fin 3`, moved to `Fin 6` along the canonical bijection.
  let e : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv
  let K : SimpleGraph (Fin 3 ⊕ Fin 3) := completeBipartiteGraph (Fin 3) (Fin 3)
  let G : SimpleGraph (Fin 6) := K.map e
  let φ : K ≃g G := Iso.map e K
  have htransport {u w : Fin 3 ⊕ Fin 3} (hadj : K.Adj u w) : G.Adj (e u) (e w) := by
    have h := (φ.map_adj_iff).mpr hadj
    rwa [Iso.map_apply e K u, Iso.map_apply e K w] at h
  have hpull {u w : Fin 6} (hadj : G.Adj u w) : K.Adj (e.symm u) (e.symm w) := by
    have hu : φ (e.symm u) = u :=
      (Iso.map_apply e K (e.symm u)).trans (e.apply_symm_apply u)
    have hw : φ (e.symm w) = w :=
      (Iso.map_apply e K (e.symm w)).trans (e.apply_symm_apply w)
    exact (φ.map_adj_iff).mp (hu.symm ▸ hw.symm ▸ hadj)
  have hKdim : HasDimension K 4 := hasDimension_completeBipartiteGraph_three_three
  refine ⟨6, G, ?_, ?_, ?_⟩
  · -- Carry dimension four from `K` along `e`.
    refine ⟨?_, ?_⟩
    · obtain ⟨f, hfInj, hfDist⟩ := hKdim.1
      refine ⟨fun x => f (e.symm x), hfInj.comp e.symm.injective, ?_⟩
      intro u v huv
      exact hfDist (e.symm u) (e.symm v) (hpull huv)
    · rw [mem_lowerBounds]
      intro m hm
      obtain ⟨g, hgInj, hgDist⟩ := hm
      exact (mem_lowerBounds.mp hKdim.2) m
        ⟨fun x => g (e x), hgInj.comp e.injective,
          fun u v huv => hgDist (e u) (e v) (htransport huv)⟩
  · -- Nine edges: `K₃,₃` has `3 * 3` of them, and `φ` preserves the count.
    have hK : K.edgeSet.ncard = 9 := by
      rw [← ENat.natCast_inj, Set.coe_ncard_eq_encard K.edgeSet,
        encard_edgeSet_completeBipartiteGraph]
      simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin]
      rw [← Nat.cast_mul]
    exact (Set.ncard_congr' φ.mapEdgeSet).symm.trans hK
  · -- Every vertex of `K₃,₃` has a neighbour, and `e` is bijective.
    intro v
    obtain ⟨w, hw⟩ : ∃ w, K.Adj (e.symm v) w := by
      cases e.symm v with
      | inl _ => exact ⟨Sum.inr 0, by simp [K]⟩
      | inr _ => exact ⟨Sum.inl 0, by simp [K]⟩
    exact ⟨e w, by simpa [e.apply_symm_apply] using htransport hw⟩
end DimensionFourExtremal.witness
end Erdos1007.Standalone.Mathlib.InlineErdos1007
