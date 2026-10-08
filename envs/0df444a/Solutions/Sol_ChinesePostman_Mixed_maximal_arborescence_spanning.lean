-- Prove2me | solution 1 for ChinesePostman.Mixed.maximal_arborescence_spanning
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:22:53.343835+00:00
-- url     : https://prove2.me/submissions/70ab74a6-50ee-405a-9d5e-32ec18e48aa1

import Mathlib
import Definitions.Def_ChinesePostman_Mixed_Setting



namespace ChinesePostman.Mixed

theorem fiber_card_aux {V E : Type} [Fintype E] [DecidableEq V] (P : E → Prop) [DecidablePred P]
    (f : E → V) (S : Finset V) :
    (Finset.univ.filter (fun e => P e ∧ f e ∈ S)).card =
      ∑ n ∈ S, (Finset.univ.filter (fun e => P e ∧ f e = n)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := S)]
  · apply Finset.sum_congr rfl
    intro n hn
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hn⟩, h3⟩
  · intro x hx
    exact (Finset.mem_filter.1 hx).2.2

theorem cut_balance_core {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : MixedGraph V E) (hsym : G.IsSymmetric) (S : Finset V) :
    (Finset.univ.filter (fun e => G.directed e = true ∧ G.tail e ∈ S ∧ G.head e ∉ S)).card =
      (Finset.univ.filter (fun e => G.directed e = true ∧ G.head e ∈ S ∧ G.tail e ∉ S)).card := by
  have hA := fiber_card_aux (fun e => G.directed e = true) G.tail S
  have hB := fiber_card_aux (fun e => G.directed e = true) G.head S
  have hAB : (Finset.univ.filter (fun e => G.directed e = true ∧ G.tail e ∈ S)).card =
      (Finset.univ.filter (fun e => G.directed e = true ∧ G.head e ∈ S)).card := by
    rw [hA, hB]
    apply Finset.sum_congr rfl
    intro n _
    exact hsym n
  have h1 : (Finset.univ.filter (fun e => G.directed e = true ∧ G.tail e ∈ S)).card =
      (Finset.univ.filter (fun e => G.directed e = true ∧ G.tail e ∈ S ∧ G.head e ∈ S)).card +
      (Finset.univ.filter (fun e => G.directed e = true ∧ G.tail e ∈ S ∧ G.head e ∉ S)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext e; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]; tauto
    · rw [Finset.disjoint_filter]; intro e _ h1 h2; exact h2.2.2 h1.2.2
  have h2 : (Finset.univ.filter (fun e => G.directed e = true ∧ G.head e ∈ S)).card =
      (Finset.univ.filter (fun e => G.directed e = true ∧ G.head e ∈ S ∧ G.tail e ∈ S)).card +
      (Finset.univ.filter (fun e => G.directed e = true ∧ G.head e ∈ S ∧ G.tail e ∉ S)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext e; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]; tauto
    · rw [Finset.disjoint_filter]; intro e _ h1 h2; exact h2.2.2 h1.2.2
  have h3 : (Finset.univ.filter (fun e => G.directed e = true ∧ G.tail e ∈ S ∧ G.head e ∈ S)) =
      (Finset.univ.filter (fun e => G.directed e = true ∧ G.head e ∈ S ∧ G.tail e ∈ S)) := by
    ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
  rw [h3] at h1
  omega

theorem arb_spanning_core {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : MixedGraph V E) (hsym : G.IsSymmetric) (hconn : G.DirectedConnected)
    (W : Finset V) (r : V) (a : V → Option E) (harb : G.IsArborescence W r a)
    (hmax : G.IsMaximalNodeSet W) :
    W = Finset.univ := by
  have hrW : r ∈ W := harb.1
  have hcut := cut_balance_core G hsym W
  have hzero : (Finset.univ.filter (fun e => G.directed e = true ∧ G.head e ∈ W ∧ G.tail e ∉ W)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e _ h
    exact h.2.2 (hmax e h.1 h.2.1)
  rw [hzero, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hcut
  have key : ∀ e, G.directed e = true → (G.tail e ∈ W ↔ G.head e ∈ W) := by
    intro e he
    constructor
    · intro ht
      by_contra hh
      exact hcut (Finset.mem_univ e) ⟨he, ht, hh⟩
    · intro hh; exact hmax e he hh
  apply Finset.eq_univ_of_forall
  intro j
  obtain ⟨ns, es, ⟨hlen, hw⟩, hhead, hlast⟩ := hconn r j
  have hall : ∀ i (h : i < ns.length), ns[i] ∈ W := by
    intro i
    induction i with
    | zero =>
      intro h
      have : ns[0] = r := by
        cases ns with
        | nil => simp at h
        | cons x xs => simpa using hhead
      rw [this]; exact hrW
    | succ k ih =>
      intro h
      have hk : k < es.length := by omega
      have hk' : k < ns.length := by omega
      obtain ⟨hP, hor⟩ := hw k hk
      have := ih hk'
      rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := (key _ hP).1 (h1 ▸ this)
        rwa [h2] at this
      · have := (key _ hP).2 (h2 ▸ this)
        rwa [h1] at this
  have hne : ns ≠ [] := by intro h; subst h; simp at hhead
  have := hall (ns.length - 1) (by have := List.length_pos_iff.mpr hne; omega)
  rw [List.getLast?_eq_getElem?] at hlast
  have hl : ns[ns.length - 1]? = some ns[ns.length - 1] := by
    rw [List.getElem?_eq_getElem]
  rw [hl] at hlast
  have := Option.some.inj hlast
  rw [← this]
  exact hall _ _

end ChinesePostman.Mixed

open ChinesePostman.Mixed


theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : MixedGraph V E) (hsym : G.IsSymmetric) (hconn : G.DirectedConnected)
    (W : Finset V) (r : V) (a : V → Option E) (harb : G.IsArborescence W r a)
    (hmax : G.IsMaximalNodeSet W) :
    W = Finset.univ := by
  exact arb_spanning_core G hsym hconn W r a harb hmax
