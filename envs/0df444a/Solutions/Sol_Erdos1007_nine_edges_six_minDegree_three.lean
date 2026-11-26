-- Prove2me | solution 1 for Erdos1007.nine_edges_six_minDegree_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:55:13.462288+00:00
-- url     : https://prove2.me/submissions/610500b1-16a6-42ae-88b5-031d8dd831d4

module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Definitions.Def_Erdos1007_Combinatorics_SimpleGraph_TwoRegularSix
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Order.BooleanAlgebra.Basic
public import Definitions.Def_Erdos1007_Combinatorics_SimpleGraph_SixVertices
public import Theorems.Thm_Erdos1007_isRegularOfDegree_two_fin_six

section
namespace Erdos1007
open SimpleGraph
private lemma isRegularOfDegree_three_of_nine_edges
    {G : SimpleGraph (Fin 6)} [DecidableRel G.Adj]
    (hE : G.edgeFinset.card = 9) (hdeg : ∀ v, 3 ≤ G.degree v) :
    G.IsRegularOfDegree 3 := by
  have hdegSum : ∑ v, G.degree v = 18 := by
    rw [G.sum_degrees_eq_twice_card_edges, hE]
  have hthree : ∑ v : Fin 6, (3 : ℕ) = 18 := by
    rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ, Fintype.card_fin]
  have hle : ∀ v ∈ Finset.univ, (3 : ℕ) ≤ G.degree v := fun v _ => hdeg v
  intro v
  have hv :=
    (Finset.sum_eq_sum_iff_of_le hle).mp (hthree.trans hdegSum.symm) v (Finset.mem_univ v)
  exact hv.symm
private lemma compl_sum_top_eq_completeBipartiteGraph :
    ((⊤ : SimpleGraph (Fin 3)) ⊕g (⊤ : SimpleGraph (Fin 3)))ᶜ =
      completeBipartiteGraph (Fin 3) (Fin 3) := by
  ext u v
  rcases u with a | a <;> rcases v with b | b
  · simp [compl_adj, top_adj, completeBipartiteGraph_adj]
  · simp [compl_adj, completeBipartiteGraph_adj]
  · simp [compl_adj, completeBipartiteGraph_adj]
  · simp [compl_adj, top_adj, completeBipartiteGraph_adj]
@[expose] public section
end
end Erdos1007
end

set_option autoImplicit false
@[expose] public section
open Erdos1007
open SimpleGraph
public section
namespace Erdos1007
theorem _root_.solution
    {G : SimpleGraph (Fin 6)} [DecidableRel G.Adj]
    (hE : G.edgeFinset.card = 9) (hdeg : ∀ v, 3 ≤ G.degree v) :
    Nonempty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∨
      Nonempty (Gᶜ ≃g cycleGraph 6) := by
  have hreg : G.IsRegularOfDegree 3 :=
    isRegularOfDegree_three_of_nine_edges hE hdeg
  have hcomplDeg : Gᶜ.IsRegularOfDegree (Fintype.card (Fin 6) - 1 - 3) :=
    IsRegularOfDegree.compl hreg
  have htwo : Fintype.card (Fin 6) - 1 - 3 = 2 := by rw [Fintype.card_fin]
  have hcompl : Gᶜ.IsRegularOfDegree 2 := htwo ▸ hcomplDeg
  rcases isRegularOfDegree_two_fin_six Gᶜ hcompl with hC | hT
  · exact Or.inr hC
  · obtain ⟨e⟩ := hT
    exact Or.inl ⟨Iso.comp (isoOfEq compl_sum_top_eq_completeBipartiteGraph)
      (isoOfComplIso e)⟩
end Erdos1007
