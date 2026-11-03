-- Prove2me | solution 1 for ChenPairedDomination.Interval.observation_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:23:59.165063+00:00
-- url     : https://prove2.me/submissions/37ff5199-5f97-4523-a14b-38ac9ff9c22d

import Definitions.Def_ChenPairedDomination_Interval_PrefixData

open ChenPairedDomination.Interval

namespace Obs6Proof

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

end Obs6Proof

open Obs6Proof in
theorem solution
    {n : ℕ} (G : SimpleGraph (Fin n))
    (R : ChenPairedDomination.Interval.OrderedRepresentation G) (hconn : G.Connected)
    (r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) :
    (G.induce (↑(ChenPairedDomination.Interval.prefixVertices (n := n) r) : Set (Fin n))).Connected := by
  let U : Set (Fin n) := ↑(prefixVertices (n := n) r)
  have hz0_lt : 0 < n := by omega
  let z0 : Fin n := ⟨0, hz0_lt⟩
  have hz0_mem : z0 ∈ U := by
    simp only [U, Finset.mem_coe, prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and, z0]
    omega
  let u0 : U := ⟨z0, hz0_mem⟩
  have : Nonempty U := ⟨u0⟩
  have hreach_from_u0 : ∀ k : ℕ, ∀ (v : Fin n) (hv : v ∈ U), v.val = k →
      (G.induce U).Reachable u0 ⟨v, hv⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v hv hvk
      by_cases hk0 : k = 0
      · have hv_eq : (⟨v, hv⟩ : U) = u0 := by
          ext
          dsimp [u0, z0]
          omega
        rw [hv_eq]
      · have hv_pos : 0 < v.val := by omega
        obtain ⟨u, huv, hadj⟩ := exists_earlier_neighbor G R hconn v hv_pos
        have hv_lt_r : v.val < r := by
          simpa [U, prefixVertices] using hv
        have hu_mem : u ∈ U := by
          simp only [U, Finset.mem_coe, prefixVertices, Finset.mem_filter, Finset.mem_univ, true_and]
          exact lt_trans huv hv_lt_r
        have hu_reach : (G.induce U).Reachable u0 ⟨u, hu_mem⟩ :=
          ih u.val (by omega) u hu_mem rfl
        have hadj_ind : (G.induce U).Adj ⟨u, hu_mem⟩ ⟨v, hv⟩ := hadj
        exact hu_reach.trans hadj_ind.reachable
  refine SimpleGraph.Connected.mk (fun a b => ?_)
  exact (hreach_from_u0 a.1.val a.1 a.2 rfl).symm.trans (hreach_from_u0 b.1.val b.1 b.2 rfl)
