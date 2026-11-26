-- Prove2me | solution 1 for Erdos1007.Standalone.Mathlib.InlineErdos1007.DimensionFourExtremal.drop3.proof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:56:43.749995+00:00
-- url     : https://prove2.me/submissions/5157c201-9d94-45d5-b28e-0881a1427531

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
public import Theorems.Thm_Erdos1007_Standalone_Mathlib_InlineErdos1007_completeBipartiteGraph_three_three_edgeSet_ncard
public import Theorems.Thm_Erdos1007_completeBipartiteGraph_three_three_unitDistance_with_left
public import Theorems.Thm_Erdos1007_not_exists_completeBipartiteGraph_three_three_unitDistance_three
public import Theorems.Thm_Erdos1007_unitDistance_of_fin_le
public import Theorems.Thm_Erdos1007_unitDistance_of_le


set_option autoImplicit false
@[expose] public section
public section
open Erdos1007 Erdos1007.Standalone Erdos1007.Standalone.Mathlib Erdos1007.Standalone.Mathlib.InlineErdos1007
open SimpleGraph
namespace Erdos1007.Standalone.Mathlib.InlineErdos1007
namespace DimensionFourExtremal.drop3
theorem _root_.solution : DimensionFourExtremal.drop3 := by
  intro hyp
  let e : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv
  let K : SimpleGraph (Fin 3 ⊕ Fin 3) := completeBipartiteGraph (Fin 3) (Fin 3)
  let a : Fin 3 ⊕ Fin 3 := Sum.inl 0
  let b : Fin 3 ⊕ Fin 3 := Sum.inl 2
  let H : SimpleGraph (Fin 3 ⊕ Fin 3) := K ⊔ edge a b
  let G : SimpleGraph (Fin 6) := H.map e
  let φ : H ≃g G := Iso.map e H
  have htransport {u w : Fin 3 ⊕ Fin 3} (hadj : H.Adj u w) : G.Adj (e u) (e w) := by
    have h := (φ.map_adj_iff).mpr hadj
    rwa [Iso.map_apply e H u, Iso.map_apply e H w] at h
  have hpull {u w : Fin 6} (hadj : G.Adj u w) : H.Adj (e.symm u) (e.symm w) := by
    have hu : φ (e.symm u) = u :=
      (Iso.map_apply e H (e.symm u)).trans (e.apply_symm_apply u)
    have hw : φ (e.symm w) = w :=
      (Iso.map_apply e H (e.symm w)).trans (e.apply_symm_apply w)
    exact (φ.map_adj_iff).mp (hu.symm ▸ hw.symm ▸ hadj)
  have hne : a ≠ b := by decide
  have hnotK : ¬ K.Adj a b := by
    simp [K, completeBipartiteGraph, a, b, Sum.isLeft, Sum.isRight]
  have hdisj : Disjoint K.edgeSet (edge a b).edgeSet := by
    rw [edgeSet_edge_of_ne hne, Set.disjoint_singleton_right, mem_edgeSet]
    exact hnotK
  have hH : H.edgeSet.ncard = 10 := by
    have hunion : H.edgeSet = K.edgeSet ∪ (edge a b).edgeSet := by
      simp [H, edgeSet_sup]
    rw [hunion, Set.ncard_union_eq hdisj,
      completeBipartiteGraph_three_three_edgeSet_ncard, edgeSet_edge_of_ne hne,
      Set.ncard_singleton]
  have hG : G.edgeSet.ncard = 10 := (Set.ncard_congr' φ.mapEdgeSet).symm.trans hH
  have hdim : HasDimension G 4 := by
    refine ⟨?_, ?_⟩
    · obtain ⟨f, hfInj, hfCross, hfLeft⟩ :=
        completeBipartiteGraph_three_three_unitDistance_with_left
      refine ⟨fun x => f (e.symm x), hfInj.comp e.symm.injective, ?_⟩
      intro u v huv
      have hHu : H.Adj (e.symm u) (e.symm v) := hpull huv
      simp only [H, sup_adj, edge_adj a b] at hHu
      rcases hHu with hK | ⟨hor, _⟩
      · exact hfCross _ _ hK
      · rcases hor with ⟨hu, hv⟩ | ⟨hu, hv⟩
        · change dist (f (e.symm u)) (f (e.symm v)) = 1
          rw [hu, hv]
          exact hfLeft
        · change dist (f (e.symm u)) (f (e.symm v)) = 1
          rw [PseudoMetricSpace.dist_comm, hu, hv]
          exact hfLeft
    · rw [mem_lowerBounds]
      intro m hm
      obtain ⟨g, hgInj, hgDist⟩ := hm
      have hHrep :
          ∃ f : Fin 3 ⊕ Fin 3 → EuclideanSpace ℝ (Fin m),
            Function.Injective f ∧ ∀ u v, H.Adj u v → dist (f u) (f v) = 1 :=
        ⟨fun x => g (e x), hgInj.comp e.injective,
          fun u v huv => hgDist (e u) (e v) (htransport huv)⟩
      have hKrep := unitDistance_of_le (le_sup_left : K ≤ H) hHrep
      have hmle : ¬ m ≤ 3 := fun hle =>
        not_exists_completeBipartiteGraph_three_three_unitDistance_three
          (unitDistance_of_fin_le hle hKrep)
      exact Nat.succ_le_of_lt (Nat.gt_of_not_le hmle)
  have hnbr : ∀ v : Fin 6, ∃ w : Fin 6, G.Adj v w := by
    intro v
    obtain ⟨w, hw⟩ : ∃ w, K.Adj (e.symm v) w := by
      cases e.symm v with
      | inl _ => exact ⟨Sum.inr 0, by simp [K, completeBipartiteGraph]⟩
      | inr _ => exact ⟨Sum.inl 0, by simp [K, completeBipartiteGraph]⟩
    exact ⟨e w, by
      simpa [e.apply_symm_apply] using htransport ((le_sup_left : K ≤ H) hw)⟩
  have hnot : ¬ Nonempty (G ≃g K) := by
    intro ⟨ψ⟩
    have hc := Set.ncard_congr' ψ.mapEdgeSet
    rw [hG, completeBipartiteGraph_three_three_edgeSet_ncard] at hc
    exact absurd hc (by decide : (10 : ℕ) ≠ 9)
  exact hnot (hyp 6 G hdim hnbr)
end DimensionFourExtremal.drop3
end Erdos1007.Standalone.Mathlib.InlineErdos1007
