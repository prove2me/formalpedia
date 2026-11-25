-- Prove2me | solution 1 for CliqueMinors.card_edge_contract
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:34:48.306301+00:00
-- url     : https://prove2.me/submissions/6bb84c5b-fa5d-4133-9b23-f86b938265d0

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Theorems.Thm_CliqueMinors_contractG_adj

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V : Type*}
open scoped Classical
variable [Fintype V]
namespace CliqueMinors
theorem _root_.solution {G : SimpleGraph V} {x y : V} (hxy : G.Adj x y) :
    G.edgeFinset.card ≤ (contractG G x y).edgeFinset.card + 1 +
      (G.neighborFinset x ∩ G.neighborFinset y).card := by
  set E1 := G.edgeFinset.filter (fun e => y ∉ e)
  set T := G.neighborFinset y \ insert x (G.neighborFinset x)
  have h1 : E1 ∪ T.image (fun v => s(x, v)) ⊆ (contractG G x y).edgeFinset := by
    intro e he
    rcases Finset.mem_union.1 he with he | he
    · rw [Finset.mem_filter] at he
      obtain ⟨he, hy⟩ := he
      induction e using Sym2.ind with
      | _ a b =>
        have hab : G.Adj a b := by simpa using he
        simp only [Sym2.mem_iff, not_or] at hy
        simp only [mem_edgeFinset, mem_edgeSet]
        exact contractG_adj.2 ⟨hab.ne, Ne.symm hy.1, Ne.symm hy.2, Or.inl hab⟩
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
      simp only [T, Finset.mem_sdiff, Finset.mem_insert, mem_neighborFinset, not_or] at hv
      simp only [mem_edgeFinset, mem_edgeSet]
      exact contractG_adj.2 ⟨Ne.symm hv.2.1, hxy.ne, hv.1.ne.symm, Or.inr (Or.inl ⟨rfl, hv.1⟩)⟩
  have hdisj : Disjoint E1 (T.image (fun v => s(x, v))) := by
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he'
    simp only [T, Finset.mem_sdiff, Finset.mem_insert, mem_neighborFinset, not_or] at hv
    rw [Finset.mem_filter] at he
    exact hv.2.2 (by simpa using he.1)
  have himg : (T.image (fun v => s(x, v))).card = T.card :=
    Finset.card_image_of_injective _ (fun a b h => Sym2.congr_right.1 h)
  have hE1 : G.edgeFinset.card = E1.card + G.degree y := by
    rw [← card_incidenceFinset_eq_degree, incidenceFinset_eq_filter,
      Finset.card_filter_add_card_filter_not (s := G.edgeFinset) (p := fun e => y ∉ e) |>.symm]
    simp [E1]
  have hT : G.degree y ≤ T.card + 1 + (G.neighborFinset x ∩ G.neighborFinset y).card := by
    have h2 : T.card + (G.neighborFinset y ∩ insert x (G.neighborFinset x)).card =
        (G.neighborFinset y).card := Finset.card_sdiff_add_card_inter _ _
    have h3 : G.neighborFinset y ∩ insert x (G.neighborFinset x) ⊆
        insert x (G.neighborFinset x ∩ G.neighborFinset y) := by
      intro v hv
      simp only [Finset.mem_inter, Finset.mem_insert] at hv ⊢
      tauto
    have h4 := (Finset.card_le_card h3).trans (Finset.card_insert_le _ _)
    rw [← card_neighborFinset_eq_degree]
    omega
  have h5 := Finset.card_le_card h1
  rw [Finset.card_union_of_disjoint hdisj, himg] at h5
  omega
end CliqueMinors
