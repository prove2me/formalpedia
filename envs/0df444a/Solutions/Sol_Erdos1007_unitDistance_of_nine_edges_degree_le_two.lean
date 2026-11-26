-- Prove2me | solution 1 for Erdos1007.unitDistance_of_nine_edges_degree_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:56:08.752072+00:00
-- url     : https://prove2.me/submissions/041816aa-c6da-45de-958f-0267f5af2d3d

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_Erdos1007_Geometry_EightEdges
public import Definitions.Def_Erdos1007_Geometry_Reattach
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Definitions.Def_Erdos1007_Geometry_LowDegree
public import Theorems.Thm_Erdos1007_unitDistance_extend_degree_le_two
public import Theorems.Thm_Erdos1007_unitDistance_of_edgeFinset_card_le_eight

section
namespace Erdos1007
open SimpleGraph Metric
private lemma card_edgeFinset_induce_ne {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (u : V) :
    (G.induce {v | v ≠ u}).edgeFinset.card = G.edgeFinset.card - G.degree u := by
  rw [← G.card_edgeFinset_deleteIncidenceSet u,
    ← G.card_edgeFinset_induce_compl_singleton u]
  rfl
@[expose] public section
end
end Erdos1007
end

set_option autoImplicit false
@[expose] public section
open Erdos1007
open SimpleGraph Metric
public section
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
namespace Erdos1007
theorem _root_.solution
    {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hE : G.edgeFinset.card = 9) {u : V} (hdeg : G.degree u ≤ 2)
    (hpos : 0 < G.degree u) :
    ∃ f : V → EuclideanSpace ℝ (Fin 3), Function.Injective f ∧
      ∀ a b, G.Adj a b → dist (f a) (f b) = 1 := by
  classical
  have glue (H : SimpleGraph {v // v ≠ u}) [DecidableRel H.Adj]
      (hsub : ∀ ⦃a b : {v // v ≠ u}⦄,
        (G.induce {v | v ≠ u}).Adj a b → H.Adj a b)
      (hextra : ∀ ⦃a b : {v // v ≠ u}⦄, G.degree u = 2 → a.1 ∈ G.neighborSet u →
        b.1 ∈ G.neighborSet u → a ≠ b → H.Adj a b)
      (hEle : H.edgeFinset.card ≤ 8) :
      ∃ f : V → EuclideanSpace ℝ (Fin 3), Function.Injective f ∧
        ∀ a b, G.Adj a b → dist (f a) (f b) = 1 := by
    classical
    obtain ⟨f, hfInj, hfDist⟩ := unitDistance_of_edgeFinset_card_le_eight (G := H) hEle
    refine unitDistance_extend_degree_le_two hdeg ⟨f, hfInj, ?_⟩
    intro a b hcond
    rcases hcond with hadj | ⟨h2, haN, hbN, hab⟩
    · exact hfDist a b (hsub hadj)
    · exact hfDist a b (hextra h2 haN hbN hab)
  obtain h1 | h2 : G.degree u = 1 ∨ G.degree u = 2 := by omega
  · let H : SimpleGraph {v // v ≠ u} := G.induce {v | v ≠ u}
    have hEle : H.edgeFinset.card ≤ 8 := by
      rw [card_edgeFinset_induce_ne (G := G) u]
      omega
    exact glue H (fun _ _ h => h) (fun _ _ h2 _ _ _ => by omega) hEle
  · let G' : SimpleGraph {v // v ≠ u} := G.induce {v | v ≠ u}
    have hNcard : (G.neighborFinset u).card = 2 := by
      rw [G.card_neighborFinset_eq_degree, h2]
    obtain ⟨a, b, _, hN⟩ := Finset.card_eq_two.mp hNcard
    have ha : G.Adj u a := (G.mem_neighborFinset u a).mp (by simp [hN])
    have hb : G.Adj u b := (G.mem_neighborFinset u b).mp (by simp [hN])
    let a' : {v // v ≠ u} := ⟨a, ha.ne'⟩
    let b' : {v // v ≠ u} := ⟨b, hb.ne'⟩
    let E : SimpleGraph {v // v ≠ u} := fromRel fun x y => x = a' ∧ y = b'
    let H : SimpleGraph {v // v ≠ u} := G' ⊔ E
    have hHcard : H.edgeFinset.card ≤ G'.edgeFinset.card + 1 := by
      have hsub : H.edgeFinset ⊆ G'.edgeFinset ∪ {s(a', b')} := by
        intro e he
        have heSet : e ∈ H.edgeSet := (mem_edgeFinset (G := H)).mp he
        induction e using Sym2.ind with
        | h x y =>
          have hadj : H.Adj x y := (mem_edgeSet (G := H)).mp heSet
          simp only [H, sup_adj] at hadj
          rcases hadj with hG | ⟨_, hpair⟩
          · exact Finset.mem_union_left _ ((mem_edgeFinset (G := G')).mpr
              ((mem_edgeSet (G := G')).mpr hG))
          · rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
            · rw [Sym2.eq_swap]
              exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
      have hunion : (G'.edgeFinset ∪ {s(a', b')}).card ≤ G'.edgeFinset.card + 1 := by
        exact (Finset.card_union_le _ _).trans (by simp)
      exact (Finset.card_le_card hsub).trans hunion
    have hEle : H.edgeFinset.card ≤ 8 := by
      have hG' : G'.edgeFinset.card = G.edgeFinset.card - 2 := by
        rw [card_edgeFinset_induce_ne (G := G) u, h2]
      omega
    exact glue H (fun _ _ h => (le_sup_left : G' ≤ H) h)
      (fun x y _ hxN hyN hxy => by
        have hxab : x.1 = a ∨ x.1 = b := by
          have hxFin : x.1 ∈ G.neighborFinset u :=
            (G.mem_neighborFinset u x.1).mpr ((G.mem_neighborSet u x.1).mp hxN)
          rw [hN] at hxFin
          simpa using hxFin
        have hyab : y.1 = a ∨ y.1 = b := by
          have hyFin : y.1 ∈ G.neighborFinset u :=
            (G.mem_neighborFinset u y.1).mpr ((G.mem_neighborSet u y.1).mp hyN)
          rw [hN] at hyFin
          simpa using hyFin
        have hEadj : E.Adj x y := by
          rw [fromRel_adj]
          refine ⟨hxy, ?_⟩
          rcases hxab with hxa | hxb <;> rcases hyab with hya | hyb
          · exact absurd (Subtype.ext (hxa.trans hya.symm)) hxy
          · exact Or.inl ⟨Subtype.ext hxa, Subtype.ext hyb⟩
          · exact Or.inr ⟨Subtype.ext hya, Subtype.ext hxb⟩
          · exact absurd (Subtype.ext (hxb.trans hyb.symm)) hxy
        exact (le_sup_right : E ≤ H) hEadj)
      hEle
end Erdos1007
