-- Prove2me | solution 1 for Balinski61.Whitney.sufficiency
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:05:44.025901+00:00
-- url     : https://prove2.me/submissions/338c2af0-21a2-478d-90e5-e080d36cb938

import Mathlib
import Definitions.Def_Balinski61_Whitney_Graph

set_option autoImplicit false
open Balinski61.Whitney

namespace BAWAux

variable {V : Type*}

lemma lift_walk (G : SimpleGraph V) (T : Set V) {a b : ↥T} (W : (G.induce T).Walk a b) :
    ∃ W' : G.Walk a.1 b.1, ∀ x ∈ W'.support, x ∈ T := by
  induction W with
  | @nil a => exact ⟨SimpleGraph.Walk.nil, fun x hx => by
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
      rw [hx]; exact a.2⟩
  | @cons a b c h W ih =>
    obtain ⟨W', hW'⟩ := ih
    refine ⟨SimpleGraph.Walk.cons (show G.Adj a.1 b.1 from h) W', ?_⟩
    intro x hx
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact a.2
    · exact hW' x hx

lemma walk_avoid (G : SimpleGraph V) (S : Finset V)
    (h : (G.induce ((↑S : Set V)ᶜ)).Connected) (u v : V) (hu : u ∉ S) (hv : v ∉ S) :
    ∃ W : G.Walk u v, ∀ x ∈ W.support, x ∉ S := by
  obtain ⟨W⟩ := h.preconnected ⟨u, fun h' => hu (Finset.mem_coe.mp h')⟩
    ⟨v, fun h' => hv (Finset.mem_coe.mp h')⟩
  obtain ⟨W', hW'⟩ := lift_walk G _ W
  exact ⟨W', fun x hx h' => hW' x hx (Finset.mem_coe.mpr h')⟩

lemma connected_of_walks (G : SimpleGraph V) (S : Finset V) (hne : ∃ v, v ∉ S)
    (h : ∀ u v, u ∉ S → v ∉ S → ∃ W : G.Walk u v, ∀ x ∈ W.support, x ∉ S) :
    (G.induce ((↑S : Set V)ᶜ)).Connected := by
  obtain ⟨v0, hv0⟩ := hne
  haveI : Nonempty (↥((↑S : Set V)ᶜ)) := ⟨⟨v0, fun h' => hv0 (Finset.mem_coe.mp h')⟩⟩
  refine ⟨fun a b => ?_⟩
  have ha : a.1 ∉ S := fun h' => a.2 (Finset.mem_coe.mpr h')
  have hb : b.1 ∉ S := fun h' => b.2 (Finset.mem_coe.mpr h')
  obtain ⟨W, hW⟩ := h a.1 b.1 ha hb
  exact ⟨W.induce _ (fun x hx => by simpa using hW x hx)⟩

lemma pigeon [Fintype V] [DecidableEq V] (G : SimpleGraph V) {n : ℕ} {ps pk : V}
    (P : Fin n → G.Walk ps pk)
    (hdis : ∀ i j, i ≠ j → ∀ x, x ∈ (P i).support → x ∈ (P j).support → x = ps ∨ x = pk)
    (X : Finset V) (hps : ps ∉ X) (hpk : pk ∉ X) :
    n ≤ X.card + (Finset.univ.filter (fun i : Fin n => ∀ x ∈ X, x ∉ (P i).support)).card := by
  classical
  have hB : (Finset.univ.filter (fun i : Fin n => ¬ ∀ x ∈ X, x ∉ (P i).support)).card ≤ X.card := by
    apply Finset.card_le_card_of_injOn
      (fun i => if h : ∃ x ∈ X, x ∈ (P i).support then h.choose else ps)
    · intro i hi
      have hi' : ∃ x ∈ X, x ∈ (P i).support := by simpa using hi
      simp only [Finset.mem_coe]
      rw [dif_pos hi']
      exact hi'.choose_spec.1
    · intro i hi j hj hij
      have hi' : ∃ x ∈ X, x ∈ (P i).support := by simpa using hi
      have hj' : ∃ x ∈ X, x ∈ (P j).support := by simpa using hj
      simp only [dif_pos hi', dif_pos hj'] at hij
      by_contra hne
      have h1 := hi'.choose_spec
      have h2 := hj'.choose_spec
      rw [hij] at h1
      rcases hdis i j hne _ h1.2 h2.2 with h | h
      · exact hps (h ▸ h2.1)
      · exact hpk (h ▸ h2.1)
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i : Fin n => ∀ x ∈ X, x ∉ (P i).support)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  omega

end BAWAux

lemma BAWAux.walk_eq_of_length_one {V : Type*} {G : SimpleGraph V} {u v : V} (p q : G.Walk u v)
    (hp : p.length = 1) (hq : q.length = 1) : p = q := by
  cases p with
  | nil => simp at hp
  | cons h p' =>
    cases p' with
    | nil =>
      cases q with
      | nil => simp at hq
      | cons h2 q' =>
        cases q' with
        | nil => rfl
        | cons _ _ => simp at hq
    | cons _ _ => simp at hp

theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V) (n : ℕ)
    (hcard : 2 ≤ Fintype.card V)
    (hpaths : ∀ ps pk : V, ps ≠ pk → HasNDisjointPaths G n ps pk) :
    IsNTuplyConnected G n := by
  classical
  have hcardn : n + 1 ≤ Fintype.card V := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨ps, pk, hne⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card V)
    obtain ⟨P, hinj, hpath, hdis⟩ := hpaths ps pk hne
    let X : Finset V := ({ps, pk} : Finset V)ᶜ
    have hX : X.card = Fintype.card V - 2 := by
      rw [Finset.card_compl, Finset.card_pair hne]
    have hps : ps ∉ X := by simp [X]
    have hpk : pk ∉ X := by simp [X]
    have hp := BAWAux.pigeon G P hdis X hps hpk
    have hgood : 1 < (Finset.univ.filter (fun i : Fin n => ∀ x ∈ X, x ∉ (P i).support)).card := by
      omega
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hgood
    have hlen : ∀ k, k ∈ Finset.univ.filter (fun i : Fin n => ∀ x ∈ X, x ∉ (P i).support) →
        (P k).length = 1 := by
      intro k hk
      have hk' := (Finset.mem_filter.mp hk).2
      have hsub : (P k).support.toFinset ⊆ {ps, pk} := by
        intro x hx
        rw [List.mem_toFinset] at hx
        by_contra hx'
        exact hk' x (Finset.mem_compl.mpr hx') hx
      have hnd := (hpath k).support_nodup
      have hc := Finset.card_le_card hsub
      rw [List.toFinset_card_of_nodup hnd, SimpleGraph.Walk.length_support] at hc
      have h2 := Finset.card_le_two (a := ps) (b := pk)
      have h0 : (P k).length ≠ 0 := fun h0 => hne (SimpleGraph.Walk.eq_of_length_eq_zero h0)
      omega
    exact hij (hinj (BAWAux.walk_eq_of_length_one _ _ (hlen i hi) (hlen j hj)))
  refine ⟨hcardn, fun X hX => ?_⟩
  apply BAWAux.connected_of_walks
  · by_contra h
    push_neg at h
    have : (Finset.univ : Finset V) ⊆ X := fun v _ => h v
    have := Finset.card_le_card this
    rw [Finset.card_univ] at this
    omega
  · intro u v hu hv
    by_cases huv : u = v
    · subst huv
      exact ⟨SimpleGraph.Walk.nil, by simpa using hu⟩
    · obtain ⟨P, hinj, hpath, hdis⟩ := hpaths u v huv
      have hp := BAWAux.pigeon G P hdis X hu hv
      obtain ⟨i, hi⟩ : ∃ i, i ∈ Finset.univ.filter (fun i : Fin n => ∀ x ∈ X, x ∉ (P i).support) :=
        Finset.card_pos.mp (by omega)
      exact ⟨P i, fun x hx hxX => (Finset.mem_filter.mp hi).2 x hxX hx⟩
