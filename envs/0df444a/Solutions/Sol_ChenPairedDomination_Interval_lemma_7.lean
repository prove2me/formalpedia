-- Prove2me | solution 1 for ChenPairedDomination.Interval.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:23:31.375874+00:00
-- url     : https://prove2.me/submissions/760c41e0-95df-4bc5-8658-19dff6f9c9bb

import Definitions.Def_ChenPairedDomination_Interval_PrefixData

open ChenPairedDomination.Interval

namespace Lemma7Proof

private lemma obs5 {n : ℕ} (G : SimpleGraph (Fin n))
    (R : OrderedRepresentation G)
    (i j : Fin n) (hji : j < i) (hij : G.Adj i j) :
    ∀ k : Fin n, j < k → k ≤ i → G.Adj j k := by
  intro k hjk hki
  obtain ⟨x, hx_i, hx_j⟩ := (R.represents i j hji.ne').mp hij
  rw [R.represents j k hjk.ne]
  refine ⟨R.left k, ⟨R.ordered hjk.le, ?_⟩, ⟨le_rfl, R.nonempty k⟩⟩
  exact (R.ordered hki).trans (hx_i.1.trans hx_j.2)

private lemma exists_edge_across_cut {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ)
    {x y : Fin n} (p : G.Walk x y) (hx : x.val < m) (hy : m ≤ y.val) :
    ∃ u w : Fin n, u.val < m ∧ m ≤ w.val ∧ G.Adj u w := by
  induction p with
  | nil => omega
  | @cons a b c hab p' ih =>
    by_cases hb : b.val < m
    · exact ih hb hy
    · exact ⟨a, b, hx, by omega, hab⟩

private lemma exists_earlier_neighbor {n : ℕ} (G : SimpleGraph (Fin n))
    (R : OrderedRepresentation G) (hconn : G.Connected)
    (v : Fin n) (hv : 0 < v.val) :
    ∃ u : Fin n, u < v ∧ G.Adj u v := by
  let z0 : Fin n := ⟨0, by omega⟩
  obtain ⟨p⟩ := hconn z0 v
  obtain ⟨u, w, hu, hw, huw⟩ := exists_edge_across_cut G v.val p hv le_rfl
  have huv : u < v := hu
  have hvw : v ≤ w := hw
  have huw' : u < w := lt_of_lt_of_le huv hvw
  exact ⟨u, huv, obs5 G R w u huw' huw.symm v huv hvw⟩

private lemma firstNeighbor_lt_and_adj_of_ne {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n)
    (hne : firstNeighbor G i ≠ i) :
    firstNeighbor G i < i ∧ G.Adj (firstNeighbor G i) i := by
  classical
  unfold firstNeighbor at hne ⊢
  set L := (List.finRange n).filter (fun k => decide (k < i ∧ G.Adj k i))
  cases hL : L with
  | nil =>
    exfalso
    apply hne
    simp [hL]
  | cons a tl =>
    have ha : a ∈ L := by simp [hL]
    simp only [L, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at ha
    simpa [hL] using ha

private lemma not_adj_of_firstNeighbor_eq {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n)
    (heq : firstNeighbor G i = i) (k : Fin n) (hki : k < i) :
    ¬ G.Adj k i := by
  intro hadj
  have hne : firstNeighbor G i ≠ i := by
    classical
    unfold firstNeighbor
    set L := (List.finRange n).filter (fun x => decide (x < i ∧ G.Adj x i))
    have hkL : k ∈ L := by
      simp [L, hki, hadj]
    cases hL : L with
    | nil => simp [hL] at hkL
    | cons a tl =>
      have ha : a ∈ L := by simp [hL]
      simp only [L, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at ha
      simp only [List.headD_cons]
      exact ha.1.ne
  exact hne heq

private lemma perfectMatching_pair {V : Type*} [DecidableEq V] (G : SimpleGraph V) (a b : V)
    (hab : G.Adj a b) :
    ∃ M : (G.induce (({a, b} : Finset V) : Set V)).Subgraph, M.IsPerfectMatching := by
  refine ⟨⊤, SimpleGraph.Subgraph.isPerfectMatching_iff.mpr ?_⟩
  rintro ⟨v, hv⟩
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · refine ⟨⟨b, by simp⟩, by simpa using hab, ?_⟩
    rintro ⟨w, hw⟩ hvw
    simp only [SimpleGraph.Subgraph.top_adj, SimpleGraph.induce_adj] at hvw
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact (G.ne_of_adj hvw rfl).elim
    · rfl
  · refine ⟨⟨a, by simp⟩, by simpa using hab.symm, ?_⟩
    rintro ⟨w, hw⟩ hvw
    simp only [SimpleGraph.Subgraph.top_adj, SimpleGraph.induce_adj] at hvw
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · rfl
    · exact (G.ne_of_adj hvw rfl).elim

private lemma two_le_card_of_pairedDominatesOn {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (U T : Finset V) (hU : U.Nonempty) (hT : PairedDominatesOn G U T) :
    2 ≤ T.card := by
  rcases hT with ⟨_, hdom, M, hM⟩
  obtain ⟨u, hu⟩ := hU
  have hT_nonempty : T.Nonempty := by
    by_cases huT : u ∈ T
    · exact ⟨u, huT⟩
    · obtain ⟨s, hsT, _⟩ := hdom u hu huT
      exact ⟨s, hsT⟩
  obtain ⟨v, hvT⟩ := hT_nonempty
  obtain ⟨w, hvw, _⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM) ⟨v, hvT⟩
  have hadj : G.Adj v w.1 := M.adj_sub hvw
  have hne : v ≠ w.1 := G.ne_of_adj hadj
  exact Finset.one_lt_card.mpr ⟨v, hvT, w.1, w.2, hne⟩

end Lemma7Proof

open Lemma7Proof in
theorem solution
    {n : ℕ} (G : SimpleGraph (Fin n)) (R : OrderedRepresentation G)
    (hconn : G.Connected) (i : Fin n)
    (hF : firstNeighbor G i ≠ i)
    (hFF : firstNeighbor G (firstNeighbor G i) = firstNeighbor G i) :
    MinimumPairedDominatesOn G (prefixVertices (i.val + 1)) {i, firstNeighbor G i} := by
  let j := firstNeighbor G i
  obtain ⟨hji, hji_adj⟩ := firstNeighbor_lt_and_adj_of_ne G i hF
  have hj0 : j.val = 0 := by
    by_contra hj_pos
    obtain ⟨u, huj, hadj⟩ := exists_earlier_neighbor G R hconn j (by omega)
    exact not_adj_of_firstNeighbor_eq G j hFF u huj hadj
  have hi_mem : i ∈ prefixVertices (i.val + 1) := by
    simp [prefixVertices]
  have hj_mem : j ∈ prefixVertices (i.val + 1) := by
    simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_trans hji (Nat.lt_succ_self i.val)
  have hpaired : PairedDominatesOn G (prefixVertices (i.val + 1)) {i, j} := by
    refine ⟨?_, ?_, perfectMatching_pair G i j hji_adj.symm⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · intro v hv hvS
      simp only [prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hvS
      have hjv : j < v := by
        change j.val < v.val
        have : v.val ≠ 0 := by
          intro hv0
          apply hvS.2
          ext
          omega
        omega
      have hvi : v ≤ i := by
        change v.val ≤ i.val
        omega
      exact ⟨j, by simp, (obs5 G R i j hji hji_adj.symm v hjv hvi).symm⟩
  refine ⟨hpaired, ?_⟩
  intro T hT
  have h2 : 2 ≤ T.card := two_le_card_of_pairedDominatesOn G (prefixVertices (i.val + 1)) T ⟨i, hi_mem⟩ hT
  exact le_trans Finset.card_le_two h2
