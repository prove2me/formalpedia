-- Prove2me | solution 1 for Balinski61.Whitney.unit_min_cut_ge
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:05:41.83647+00:00
-- url     : https://prove2.me/submissions/5112d739-c41f-42e7-9a25-c5149f87501c

import Mathlib
import Definitions.Def_Balinski61_Whitney_Graph
import Definitions.Def_Balinski61_Whitney_Network
import Definitions.Def_Balinski61_Whitney_UnitNetwork

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

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) (ps pk : V)
    (hG : IsNTuplyConnected G n) (hst : ps ≠ pk) :
    ∀ (X : Finset V) (F : Finset (Sym2 V)), IsDisconnecting G ps pk X F →
      (n : ℝ) ≤ cutValue (unitCapV ps pk n) (unitCapE ps pk n) X F := by
  intro X F hdisc
  by_contra hlt
  push_neg at hlt
  obtain ⟨hFedge, hC⟩ := hdisc
  unfold cutValue at hlt
  have hV1 : ∀ x, 1 ≤ unitCapV ps pk n x := by
    intro x; unfold unitCapV; split_ifs
    · have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · exact le_refl _
  have hE1 : ∀ e, 1 ≤ unitCapE ps pk n e := by
    intro e; unfold unitCapE; split_ifs
    · exact le_refl _
    · have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
  have hXnn : 0 ≤ ∑ x ∈ X, unitCapV ps pk n x :=
    Finset.sum_nonneg (fun x _ => by linarith [hV1 x])
  have hFnn : 0 ≤ ∑ e ∈ F, unitCapE ps pk n e :=
    Finset.sum_nonneg (fun e _ => by linarith [hE1 e])
  have hpsc : unitCapV ps pk n ps = n + 1 := by simp [unitCapV]
  have hpkc : unitCapV ps pk n pk = n + 1 := by simp [unitCapV]
  have hpsX : ps ∉ X := by
    intro h
    have := Finset.single_le_sum (f := unitCapV ps pk n) (fun x _ => by linarith [hV1 x]) h
    linarith
  have hpkX : pk ∉ X := by
    intro h
    have := Finset.single_le_sum (f := unitCapV ps pk n) (fun x _ => by linarith [hV1 x]) h
    linarith
  have hFe : ∀ e ∈ F, e = s(ps, pk) := by
    intro e he
    by_contra hne
    have hc : unitCapE ps pk n e = n + 1 := by simp [unitCapE, hne]
    have := Finset.single_le_sum (f := unitCapE ps pk n) (fun x _ => by linarith [hE1 x]) he
    linarith
  have hXs : ∑ x ∈ X, unitCapV ps pk n x = X.card := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ))]
    · simp
    · intro x hx
      have h1 : x ≠ ps := fun h => hpsX (h ▸ hx)
      have h2 : x ≠ pk := fun h => hpkX (h ▸ hx)
      simp [unitCapV, h1, h2]
  by_cases hmem : s(ps, pk) ∈ F
  · have hFs : F = {s(ps, pk)} := by
      ext e
      constructor
      · intro he; simpa using hFe e he
      · intro he; rw [Finset.mem_singleton.mp he]; exact hmem
    have hFv : ∑ e ∈ F, unitCapE ps pk n e = 1 := by
      rw [hFs]; simp [unitCapE]
    rw [hXs, hFv] at hlt
    have hlt' : X.card + 1 < n := by exact_mod_cast hlt
    obtain ⟨w, -, hw⟩ : ∃ w ∈ (Finset.univ : Finset V), w ∉ X ∪ {ps, pk} := by
      apply Finset.exists_mem_notMem_of_card_lt_card
      have h1 : (X ∪ {ps, pk}).card ≤ X.card + 2 :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_le_two) _)
      have h2 := hG.1
      rw [Finset.card_univ]
      omega
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hw
    obtain ⟨hwX, hwps, hwpk⟩ := hw
    have hc1 := hG.2 (insert pk X) (by
      have := Finset.card_insert_le pk X
      omega)
    have hc2 := hG.2 (insert ps X) (by
      have := Finset.card_insert_le ps X
      omega)
    obtain ⟨W1, hW1⟩ := BAWAux.walk_avoid G _ hc1 ps w (by simp [hst, hpsX]) (by simp [hwX, hwpk])
    obtain ⟨W2, hW2⟩ := BAWAux.walk_avoid G _ hc2 w pk (by simp [hwps, hwX]) (by simp [hst.symm, hpkX])
    rcases hC (W1.append W2) with ⟨x, hxX, hx⟩ | ⟨e, heF, he⟩
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hx
      rcases hx with hx | hx
      · exact hW1 x hx (Finset.mem_insert_of_mem hxX)
      · exact hW2 x hx (Finset.mem_insert_of_mem hxX)
    · rw [hFe e heF, SimpleGraph.Walk.edges_append, List.mem_append] at he
      rcases he with he | he
      · exact hW1 pk (W1.snd_mem_support_of_mem_edges he) (Finset.mem_insert_self _ _)
      · exact hW2 ps (W2.fst_mem_support_of_mem_edges he) (Finset.mem_insert_self _ _)
  · have hF0 : F = ∅ := by
      ext e
      simp only [Finset.notMem_empty, iff_false]
      intro he
      exact hmem (hFe e he ▸ he)
    rw [hF0, hXs] at hlt
    simp only [Finset.sum_empty, add_zero] at hlt
    have hlt' : X.card < n := by exact_mod_cast hlt
    obtain ⟨W, hW⟩ := BAWAux.walk_avoid G X (hG.2 X hlt') ps pk hpsX hpkX
    rcases hC W with ⟨x, hxX, hx⟩ | ⟨e, heF, -⟩
    · exact hW x hx hxX
    · simp [hF0] at heF
