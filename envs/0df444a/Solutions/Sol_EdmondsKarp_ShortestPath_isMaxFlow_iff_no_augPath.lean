-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.isMaxFlow_iff_no_augPath
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T19:24:07.437253+00:00
-- url     : https://prove2.me/submissions/edcd56c4-2d38-4fb8-a5d4-10e275c237bd

import Theorems.Thm_EdmondsKarp_ShortestPath_augment_isFlow

open EdmondsKarp.ShortestPath

private theorem local_pathArcs_chain {V : Type} [Fintype V] [DecidableEq V] (R : V → V → Prop) (P : List V) :
    (∀ e ∈ pathArcs P, R e.1 e.2) ↔ P.IsChain R := by
  induction P with
  | nil => simp [pathArcs]
  | cons a L ih =>
    cases L with
    | nil => simp [pathArcs]
    | cons b L =>
      have hs : pathArcs (a :: b :: L) = (a, b) :: pathArcs (b :: L) := rfl
      rw [hs]
      simp only [List.forall_mem_cons, List.isChain_cons_cons, ih]

private theorem local_chain_simple {V : Type} [DecidableEq V] (R : V → V → Prop) (P : List V)
    (hP : P.IsChain R) :
    ∃ Q : List V, Q.Nodup ∧ Q.IsChain R ∧ Q.head? = P.head? ∧
      Q.getLast? = P.getLast? ∧ Q.length ≤ P.length := by
  induction P with
  | nil => exact ⟨[], by simp⟩
  | cons a L ih =>
    obtain ⟨Q, hnd, hc, hh, hl, hlen⟩ := ih hP.tail
    by_cases ha : a ∈ Q
    · have hi : Q.idxOf a < Q.length := List.idxOf_lt_length_iff.mpr ha
      have hL : L ≠ [] := by
        intro he
        have : Q.length = 0 := by simpa [he] using hlen
        have hQ : Q = [] := by simpa using this
        simp [hQ] at ha
      refine ⟨Q.drop (Q.idxOf a), hnd.sublist (List.drop_sublist _ _), hc.drop _, ?_, ?_, ?_⟩
      · simpa using List.getElem?_idxOf ha
      · rw [List.getLast?_drop, if_neg (by omega), hl, List.getLast?_cons_of_ne_nil hL]
      · simp only [List.length_drop, List.length_cons]
        omega
    · refine ⟨a :: Q, List.nodup_cons.mpr ⟨ha, hnd⟩, ?_, rfl, ?_, ?_⟩
      · apply hc.cons
        intro y hy
        rw [hh] at hy
        exact hP.rel_head? hy
      · simp only [List.getLast?_cons, hl]
      · simpa using hlen

private theorem local_dirPath_reachable {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (u v : V) :
    (∃ P, IsDirPath N f u v P) ↔ Relation.ReflTransGen (ResArc N f) u v := by
  constructor
  · rintro ⟨P, hnd, hh, hl, hc⟩
    have hne : P ≠ [] := by intro h; simp [h] at hh
    have hh' : P.head hne = u := by simpa [List.head?_eq_some_head hne] using hh
    have hl' : P.getLast hne = v := by simpa [List.getLast?_eq_some_getLast hne] using hl
    simpa [hh', hl'] using
      List.relationReflTransGen_of_exists_isChain P ((local_pathArcs_chain _ _).mp hc) hne
  · intro h
    obtain ⟨P, hne, hc, hh, hl⟩ := List.exists_isChain_ne_nil_of_relationReflTransGen h
    obtain ⟨Q, hnd, hchain, hhead, hlast, _⟩ := local_chain_simple (ResArc N f) P hc
    refine ⟨Q, hnd, ?_, ?_, (local_pathArcs_chain _ _).mpr hchain⟩
    · rw [hhead, List.head?_eq_some_head hne, hh]
    · rw [hlast, List.getLast?_eq_some_getLast hne, hl]

private theorem local_divergence_cut {V : Type} [Fintype V] [DecidableEq V] (d : V → V → ℝ) (S : Finset V) :
    (∑ u ∈ S, ∑ v : V, (d u v - d v u)) =
      ∑ u ∈ S, ∑ v ∈ Sᶜ, (d u v - d v u) := by
  have hsplit (u : V) : (∑ v : V, (d u v - d v u)) =
      (∑ v ∈ S, (d u v - d v u)) + (∑ v ∈ Sᶜ, (d u v - d v u)) := by
    exact (Finset.sum_add_sum_compl S (fun v => d u v - d v u)).symm
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  have hz : (∑ u ∈ S, ∑ v ∈ S, (d u v - d v u)) = 0 := by
    simp only [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (Finset.sum_comm)
  rw [hz, zero_add]

private theorem local_network_divergence {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (g : V → V → ℝ) (u : V) :
    (∑ v ∈ Finset.univ.filter (fun v => (u, v) ∈ N.arcs), g u v) -
      (∑ v ∈ Finset.univ.filter (fun v => (v, u) ∈ N.arcs), g v u) =
    (∑ v : V, if (u, v) ∈ N.A then g u v else 0) -
      (∑ v : V, if (v, u) ∈ N.A then g v u else 0) +
    (if u = N.t then g N.t N.s else 0) - (if u = N.s then g N.t N.s else 0) := by
  have heq (x y : V) :
      (if (x, y) ∈ N.arcs then g x y else 0) =
      (if (x, y) ∈ N.A then g x y else 0) +
      (if x = N.t ∧ y = N.s then g N.t N.s else 0) := by
    by_cases h : x = N.t ∧ y = N.s
    · rcases h with ⟨rfl, rfl⟩
      simp [Network.arcs, N.return_not_mem]
    · simp [Network.arcs, Prod.mk.injEq, h]
  simp only [Finset.sum_filter]
  simp_rw [heq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hout : (∑ v : V, if u = N.t ∧ v = N.s then g N.t N.s else 0) =
      (if u = N.t then g N.t N.s else 0) := by
    by_cases h : u = N.t <;> simp [h]
  have hin : (∑ v : V, if v = N.t ∧ u = N.s then g N.t N.s else 0) =
      (if u = N.s then g N.t N.s else 0) := by
    by_cases h : u = N.s <;> simp [h]
  rw [hout, hin]
  ring

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (hf : IsFlow N f) :
    IsMaxFlow N f ↔ ¬ ∃ P : List V, IsAugPath N f P := by
  classical
  constructor
  · rintro hmax ⟨P, hP⟩
    obtain ⟨he, hflow, hvalue⟩ := augment_isFlow N f P hf hP
    have hle := hmax.2 _ hflow
    rw [hvalue] at hle
    linarith
  · intro hn
    refine ⟨hf, ?_⟩
    intro g hg
    let S := Finset.univ.filter (fun u => Relation.ReflTransGen (ResArc N f) N.s u)
    have hs : N.s ∈ S := by simp [S, Relation.ReflTransGen.refl]
    have ht : N.t ∉ S := by
      intro h
      exact hn ((local_dirPath_reachable N f N.s N.t).mpr (Finset.mem_filter.mp h).2)
    have hclosed (u v : V) (hu : u ∈ S) (h : ResArc N f u v) : v ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((Finset.mem_filter.mp hu).2).tail h⟩
    let d := fun u v => if (u, v) ∈ N.A then g u v - f u v else 0
    have hcut : (∑ u ∈ S, ∑ v ∈ Sᶜ, (d u v - d v u)) ≤ 0 := by
      apply Finset.sum_nonpos
      intro u hu
      apply Finset.sum_nonpos
      intro v hv
      have hnr : ¬ ResArc N f u v := fun h => (Finset.mem_compl.mp hv) (hclosed u v hu h)
      have hout : d u v ≤ 0 := by
        by_cases huv : (u, v) ∈ N.A
        · have hcf : N.c u v ≤ f u v := le_of_not_gt fun h =>
            hnr (Or.inl ⟨huv, sub_pos.mpr h⟩)
          have hcg := hg.2.1 u v huv
          simp only [d, huv, ↓reduceIte]
          linarith
        · simp [d, huv]
      have hin : 0 ≤ d v u := by
        by_cases hvu : (v, u) ∈ N.A
        · have hcf : f v u ≤ 0 := le_of_not_gt fun h => hnr (Or.inr ⟨hvu, h⟩)
          have hcg := hg.1 v u (Finset.mem_insert_of_mem hvu)
          simp only [d, hvu, ↓reduceIte]
          linarith
        · simp [d, hvu]
      linarith
    have hbal (u : V) : (∑ v : V, (d u v - d v u)) =
        (if u = N.s then g N.t N.s - f N.t N.s else 0) -
        (if u = N.t then g N.t N.s - f N.t N.s else 0) := by
      have hbf := hf.2.2 u
      have hbg := hg.2.2 u
      rw [local_network_divergence] at hbf hbg
      have hi (a b : ℝ) (q : Prop) [Decidable q] :
          (if q then a - b else 0) = (if q then a else 0) - (if q then b else 0) := by
        split_ifs <;> simp
      dsimp only [d]
      simp_rw [hi]
      simp only [Finset.sum_sub_distrib]
      by_cases hus : u = N.s <;> by_cases hut : u = N.t <;>
        simp only [hus, hut, eq_comm, N.source_ne_sink, ↓reduceIte] at hbf hbg ⊢ <;>
        linarith
    rw [← local_divergence_cut d S] at hcut
    simp_rw [hbal] at hcut
    simpa [Finset.sum_sub_distrib, hs, ht] using hcut
