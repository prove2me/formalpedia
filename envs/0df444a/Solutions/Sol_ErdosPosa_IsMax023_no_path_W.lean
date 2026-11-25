-- Prove2me | solution 1 for ErdosPosa.IsMax023.no_path_W
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:30:46.136294+00:00
-- url     : https://prove2.me/submissions/007692ea-b971-4f5a-a259-f5aec706ac65

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPPacking
public import Definitions.Def_ErdosPosaLib_EPMaximal
public import Theorems.Thm_ErdosPosa_neighborSet_empty_of_deg_zero
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
variable [Finite V] {G H : SimpleGraph V}
namespace ErdosPosa
namespace IsMax023
theorem _root_.solution (hH : IsMax023 G H) {w1 w2 : V} (hw1 : deg H w1 = 2)
    (hw2 : deg H w2 = 2) (hne : w1 ≠ w2) (p : G.Walk w1 w2)
    (hsupp : ∀ x ∈ p.support, x = w1 ∨ x = w2 ∨ deg H x = 0)
    (hedges : ∀ e ∈ p.edges, e ∉ H.edgeSet) : False := by
  classical
  let P := p.bypass
  have hP : P.IsPath := p.bypass_isPath
  have hPs : ∀ x ∈ P.support, x ∈ p.support := fun x hx => p.support_bypass_subset_support hx
  have hPe : ∀ e ∈ P.edges, e ∈ p.edges := fun e he => p.edges_bypass_subset_edges he
  have hnil : ¬ P.Nil := fun h => hne h.eq
  let C : SimpleGraph V := P.toSubgraph.spanningCoe
  have hCnbr : ∀ a, C.neighborSet a = P.toSubgraph.neighborSet a := fun a => rfl
  have hCnotH : ∀ a b, C.Adj a b → ¬ H.Adj a b := by
    intro a b hab hH'
    have : s(a, b) ∈ P.edges := Walk.adj_toSubgraph_iff_mem_edges.1 hab
    exact hedges _ (hPe _ this) hH'
  let K := H ⊔ C
  have hKG : K ≤ G := sup_le hH.1 (fun a b h => P.toSubgraph.adj_sub h)
  -- endpoints get degree 3
  have hend : ∀ a x, deg H a = 2 → C.neighborSet a = {x} → deg K a = 3 := by
    intro a x ha hx
    have hxa : C.Adj a x := by
      have : x ∈ C.neighborSet a := by rw [hx]; rfl
      exact this
    rw [deg, neighborSet_sup, hx, Set.union_singleton, Set.ncard_insert_of_notMem]
    · rw [← deg, ha]
    · exact hCnotH a x hxa
  have hdegK : Deg023 K := by
    intro a
    by_cases ha1 : a = w1
    · subst ha1
      right; right
      exact hend a _ hw1 ((hCnbr a).trans (hP.neighborSet_toSubgraph_startpoint hnil))
    by_cases ha2 : a = w2
    · subst ha2
      right; right
      exact hend a _ hw2 ((hCnbr a).trans (hP.neighborSet_toSubgraph_endpoint hnil))
    by_cases ha : a ∈ P.support
    · have haR : deg H a = 0 := by
        rcases hsupp a (hPs a ha) with h | h | h
        · exact absurd h ha1
        · exact absurd h ha2
        · exact h
      obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.1 ha
      have hi0 : i ≠ 0 := by rintro rfl; rw [Walk.getVert_zero] at hi; exact ha1 hi.symm
      have hil' : i < P.length := by
        rcases lt_or_eq_of_le hil with h | h
        · exact h
        · subst h; rw [Walk.getVert_length] at hi; exact absurd hi.symm ha2
      right; left
      rw [deg, neighborSet_sup, neighborSet_empty_of_deg_zero haR, Set.empty_union, hCnbr, ← hi]
      exact hP.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hil'
    · have : C.neighborSet a = ∅ := by
        ext b
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hb
        exact ha ((P.mem_verts_toSubgraph).1 (Subgraph.Adj.fst_mem hb))
      have hda : deg K a = deg H a := by
        rw [deg, neighborSet_sup, this, Set.union_empty]; rfl
      rw [hda]; exact hH.2.1 a
  have hadj : C.Adj w1 P.snd := P.toSubgraph_adj_snd hnil
  exact hCnotH _ _ hadj (hH.2.2 K hKG hdegK le_sup_left w1 P.snd (Or.inr hadj))
end IsMax023
end ErdosPosa
