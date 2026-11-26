-- Prove2me | solution 1 for Erdos1007.Standalone.Mathlib.InlineErdos1007.DimensionFourExtremal.drop2.proof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:55:32.596647+00:00
-- url     : https://prove2.me/submissions/89ee7828-4b57-45ba-96c1-a340b8177340

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
namespace DimensionFourExtremal.drop2
theorem _root_.solution : DimensionFourExtremal.drop2 := by
  intro hyp
  let P : SimpleGraph (Fin 9 × Fin 2) := {
    Adj := fun u v => u.1 = v.1 ∧ u.2 ≠ v.2
    symm := ⟨fun u v h => ⟨h.1.symm, h.2.symm⟩⟩
    loopless := ⟨fun u h => h.2 rfl⟩
  }
  let e : Fin 9 × Fin 2 ≃ Fin 18 := finProdFinEquiv
  let G : SimpleGraph (Fin 18) := P.map e
  let φ : P ≃g G := Iso.map e P
  let : DecidableRel P.Adj := Classical.decRel P.Adj
  have hflip : ∀ b : Fin 2, b ≠ b + 1 := by decide
  have hother : ∀ b c : Fin 2, b ≠ c → c = b + 1 := by decide
  have hadj (u : Fin 9 × Fin 2) : P.Adj u (u.1, u.2 + 1) :=
    ⟨rfl, hflip u.2⟩
  have hdeg (u : Fin 9 × Fin 2) : P.degree u = 1 := by
    rw [← card_neighborFinset_eq_degree]
    refine Finset.card_eq_one.mpr ⟨(u.1, u.2 + 1), ?_⟩
    ext v
    simp only [mem_neighborFinset, Finset.mem_singleton]
    constructor
    · intro h
      obtain ⟨h1, hne⟩ := h
      exact Prod.ext h1.symm (hother u.2 v.2 hne)
    · rintro rfl
      exact hadj u
  have hsum : ∑ u : Fin 9 × Fin 2, P.degree u = 18 := by
    simp only [hdeg, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    norm_num
  have hP : P.edgeSet.ncard = 9 := by
    have htwice : ∑ u, P.degree u = 2 * P.edgeFinset.card :=
      P.sum_degrees_eq_twice_card_edges
    have hcard : P.edgeFinset.card = 9 := by
      rw [hsum] at htwice
      omega
    rw [Set.ncard_eq_toFinset_card' P.edgeSet]
    simpa [edgeFinset] using hcard
  have hG : G.edgeSet.ncard = 9 := (Set.ncard_congr' φ.mapEdgeSet).symm.trans hP
  have htransport {u w : Fin 9 × Fin 2} (hadj' : P.Adj u w) : G.Adj (e u) (e w) := by
    have h := (φ.map_adj_iff).mpr hadj'
    rwa [Iso.map_apply e P u, Iso.map_apply e P w] at h
  have hnbr : ∀ v : Fin 18, ∃ w : Fin 18, G.Adj v w := by
    intro v
    refine ⟨e ((e.symm v).1, (e.symm v).2 + 1), ?_⟩
    simpa [e.apply_symm_apply] using htransport (hadj (e.symm v))
  have hnot : ¬ Nonempty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := by
    intro ⟨ψ⟩
    have hc := ψ.card_eq
    simp only [Fintype.card_fin, Fintype.card_sum] at hc
    omega
  exact hnot (hyp 18 G hG hnbr)
end DimensionFourExtremal.drop2
end Erdos1007.Standalone.Mathlib.InlineErdos1007
