-- Prove2me | solution 1 for EDPHardness.IntegralityGap.canonical_paths_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T10:06:00.128916+00:00
-- url     : https://prove2.me/submissions/4ad41782-c4d6-48ca-8b4d-5c5a8a644aac

import Mathlib
import Definitions.Def_EDPHardness_IntegralityGap_FlowRelaxation
import Definitions.Def_EDPHardness_IntegralityGap_GapInstance

namespace EDPCanonBoundAux

open EDPHardness.IntegralityGap

lemma edge_of_infix {V : Type*} {G : SimpleGraph V} (x y : V) :
    ∀ {u w : V} (p : G.Walk u w) (l1 l2 : List V),
      p.support = l1 ++ x :: y :: l2 → s(x, y) ∈ p.edges := by
  intro u w p
  induction p with
  | nil =>
    intro l1 l2 h
    cases l1 with
    | nil => simp at h
    | cons a l1 => simp at h
  | @cons a b c' h p ih =>
    intro l1 l2 hs
    rw [SimpleGraph.Walk.support_cons] at hs
    cases l1 with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hs
      obtain ⟨rfl, hs⟩ := hs
      have hb : b = y := by
        have := SimpleGraph.Walk.support_eq_cons p
        rw [hs] at this
        simp only [List.cons.injEq] at this
        exact this.1.symm
      subst hb
      simp
    | cons a' l1 =>
      simp only [List.cons_append, List.cons.injEq] at hs
      rw [SimpleGraph.Walk.edges_cons]
      exact List.mem_cons_of_mem _ (ih l1 l2 hs.2)

lemma canon_infix {n m c : ℕ} (H : Hyp n m c) (v : Fin n) (i : Fin m) (hv : v ∈ (H i).1) :
    ∃ l1 l2, canonicalSupport H v = l1 ++ Node.l i :: Node.r i :: l2 := by
  have hi : i ∈ (List.finRange m).filter (fun j => decide (v ∈ (H j).1)) := by
    simp [hv]
  obtain ⟨L1, L2, hL⟩ := List.append_of_mem hi
  refine ⟨Node.s v :: L1.flatMap (fun j => [Node.l j, Node.r j]),
    L2.flatMap (fun j => [Node.l j, Node.r j]) ++ [Node.t v], ?_⟩
  unfold canonicalSupport
  rw [hL]
  simp

end EDPCanonBoundAux

open EDPHardness.IntegralityGap in
theorem solution (n c : ℕ) (hc : 2 ≤ c) (hβ₁ : 0 < beta1 n c)
    (H : Hyp n (numEdges n c) c) (hE₁ : ¬ E1 n c H)
    (R : IntRouting (gapGraph H) (src n (numEdges n c)) (snk n (numEdges n c)) (c - 1)) :
    ((Finset.univ.filter
        (fun v : R.routed => (R.path v).support = canonicalSupport H v)).card : ℝ)
      ≤ (n : ℝ) / beta1 n c := by
  classical
  set A := Finset.univ.filter
    (fun v : R.routed => (R.path v).support = canonicalSupport H v) with hA
  by_contra hlt
  push_neg at hlt
  have hbs : badSize n c ≤ A.card := Nat.ceil_le.2 hlt.le
  set S' : Finset (Fin n) := A.image Subtype.val with hS'
  have hS'card : S'.card = A.card := Finset.card_image_of_injective _ Subtype.val_injective
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (s := S') (n := badSize n c)
    (by rw [hS'card]; exact hbs)
  unfold E1 at hE₁
  push_neg at hE₁
  obtain ⟨i, hi⟩ := hE₁ T hTcard
  set e : Sym2 (Node n (numEdges n c)) := s(Node.l i, Node.r i)
  have hcong := R.congestion e
  set B := Finset.univ.filter (fun w : R.routed => e ∈ (R.path w).edges)
  have hsub : (H i).1 ⊆ B.image Subtype.val := by
    intro v hv
    have hvS : v ∈ S' := hTS (hi hv)
    rw [hS', Finset.mem_image] at hvS
    obtain ⟨w, hwA, hwv⟩ := hvS
    rw [Finset.mem_image]
    refine ⟨w, ?_, hwv⟩
    have hwA' : (R.path w).support = canonicalSupport H w := by
      simpa [hA] using hwA
    have hwi : (w : Fin n) ∈ (H i).1 := hwv ▸ hv
    obtain ⟨l1, l2, hl⟩ := EDPCanonBoundAux.canon_infix H w i hwi
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    exact EDPCanonBoundAux.edge_of_infix _ _ (R.path w) l1 l2 (hwA'.trans hl)
  have h1 : c ≤ B.card := by
    calc c = (H i).1.card := (H i).2.symm
      _ ≤ (B.image Subtype.val).card := Finset.card_le_card hsub
      _ ≤ B.card := Finset.card_image_le
  omega
