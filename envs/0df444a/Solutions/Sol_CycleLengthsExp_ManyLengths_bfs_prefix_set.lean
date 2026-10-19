-- Prove2me | solution 1 for CycleLengthsExp.ManyLengths.bfs_prefix_set
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:42:30.56423+00:00
-- url     : https://prove2.me/submissions/931f10c6-bae0-4313-af68-9d8717f811c7

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

open CycleLengthsExp CycleLengthsExp.ManyLengths
/-- BFS prefix set (Friedman–Krivelevich, p. 13: `S` is a PREFIX of a full
BFS tree — all of levels `1..m-1` plus some of level `m`).

Stated in `G`-distance terms (level = `dist + 1`, so `r = m - 1`): given a
connected graph `G` on `Fin n`, a root `v₀`, and `1 ≤ N ≤ n`, there are a set
`S` and a radius `r` such that `S` has exactly `N` vertices, contains `v₀`,
contains the whole ball of radius `r - 1`, is contained in the ball of
radius `r`, attains radius `r`, and every non-root vertex of `S` has a
parent in `S` one step closer to `v₀` (the predecessor on a shortest
`v₀`–`v` path, which lies in the ball of radius `r - 1 ⊆ S`).

Proof sketch: let `B_k = {v | dist_G(v₀, v) ≤ k}`. `B_0 = {v₀}` has size 1,
`B_k ↑ univ` (connectedness: every vertex is reachable), so let `r` be the
least `k` with `|B_k| ≥ N`; then `|B_{r-1}| < N ≤ |B_r|` (with `B_{-1} = ∅`),
and take `S = B_{r-1} ∪ (any N - |B_{r-1}| vertices of the sphere
{dist = r})`. The parent property follows from the predecessor lemma:
any reachable `v ≠ v₀` has a neighbour `u` with `dist(v₀, u) + 1 = dist(v₀, v)`
(take a shortest walk, its penultimate vertex). The predecessor lemma itself
is elementary (`Reachable.exists_walk_length_eq_dist` + `Walk.concat` /
`dropLast`) and should be proved for real inside `B`'s proof, not axiomatized. -/
theorem h42_pred {V : Type*} {G : SimpleGraph V} {v₀ v : V} (hr : G.Reachable v₀ v) (hne : v ≠ v₀) :
    ∃ u, G.Adj u v ∧ G.dist v₀ u + 1 = G.dist v₀ v := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  have hpr : p.reverse.length = G.dist v₀ v := by rw [SimpleGraph.Walk.length_reverse, hp]
  generalize p.reverse = q at hpr
  cases q with
  | nil => exact absurd rfl hne
  | @cons _ u _ h q =>
    refine ⟨u, h.symm, ?_⟩
    have h1 : G.dist u v₀ ≤ q.length := SimpleGraph.dist_le q
    rw [SimpleGraph.Walk.length_cons] at hpr
    have h2 : G.dist v₀ v ≤ G.dist v₀ u + G.dist u v := h.symm.reachable.dist_triangle_right v₀
    have h3 : G.dist u v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h.symm
    rw [SimpleGraph.dist_comm] at h1
    omega

theorem solution (n : ℕ) (G : SimpleGraph (Fin n)) (v₀ : Fin n) (N : ℕ)
    (hconn : ∀ v, G.Reachable v₀ v) (hN1 : 1 ≤ N) (hNn : N ≤ n) :
    ∃ (S : Set (Fin n)) (r : ℕ),
      S.ncard = N ∧ v₀ ∈ S ∧
      (∀ v, G.dist v₀ v ≤ r - 1 → v ∈ S) ∧
      (∀ v ∈ S, G.dist v₀ v ≤ r) ∧
      (∃ v ∈ S, G.dist v₀ v = r) ∧
      (∀ v ∈ S, v ≠ v₀ →
        ∃ u ∈ S, G.Adj u v ∧ G.dist v₀ u + 1 = G.dist v₀ v) := by
  classical
  let B : ℕ → Finset (Fin n) := fun k => Finset.univ.filter (fun v => G.dist v₀ v ≤ k)
  have hex : ∃ k, N ≤ (B k).card := by
    refine ⟨Finset.univ.sup (fun v => G.dist v₀ v), ?_⟩
    have : B (Finset.univ.sup (fun v => G.dist v₀ v)) = Finset.univ := by
      ext v; simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact Finset.le_sup (f := fun v => G.dist v₀ v) (Finset.mem_univ v)
    rw [this, Finset.card_univ, Fintype.card_fin]; exact hNn
  let r := Nat.find hex
  have hr : N ≤ (B r).card := Nat.find_spec hex
  let A : Finset (Fin n) := Finset.univ.filter (fun v => G.dist v₀ v < r)
  let Sp : Finset (Fin n) := Finset.univ.filter (fun v => G.dist v₀ v = r)
  have hA : A.card < N := by
    by_cases h0 : r = 0
    · have : A = ∅ := by
        ext v; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]; omega
      rw [this, Finset.card_empty]; omega
    · have hm := Nat.find_min hex (show r - 1 < r by omega)
      have : A = B (r - 1) := by
        ext v; simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and]; omega
      rw [this]; omega
  have hBr : B r = A ∪ Sp := by
    ext v; simp only [A, B, Sp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]; omega
  have hdisj : Disjoint A Sp := by
    rw [Finset.disjoint_left]; intro v h1 h2
    simp only [A, Sp, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2; omega
  have hSp : N - A.card ≤ Sp.card := by
    rw [hBr, Finset.card_union_of_disjoint hdisj] at hr; omega
  obtain ⟨Q, hQSp, hQcard⟩ := Finset.exists_subset_card_eq hSp
  have hQne : Q.Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨q, hq⟩ := hQne
  have hqr : G.dist v₀ q = r := by
    have := hQSp hq; simp only [Sp, Finset.mem_filter, Finset.mem_univ, true_and] at this; exact this
  have hdisjQ : Disjoint A Q := Finset.disjoint_of_subset_right hQSp hdisj
  have memS : ∀ v, v ∈ ((A ∪ Q : Finset (Fin n)) : Set (Fin n)) ↔ v ∈ A ∨ v ∈ Q := by
    intro v; simp
  have hle : ∀ v, v ∈ A ∨ v ∈ Q → G.dist v₀ v ≤ r := by
    intro v hv
    rcases hv with hv | hv
    · simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hv; omega
    · have := hQSp hv; simp only [Sp, Finset.mem_filter, Finset.mem_univ, true_and] at this; omega
  have hv₀S : v₀ ∈ A ∨ v₀ ∈ Q := by
    by_cases h0 : r = 0
    · right
      have : q = v₀ := by
        have := ((hconn q).dist_eq_zero_iff).mp (by omega); exact this.symm
      rw [← this]; exact hq
    · left; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.dist_self]; omega
  refine ⟨((A ∪ Q : Finset (Fin n)) : Set (Fin n)), r, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Set.ncard_coe_finset, Finset.card_union_of_disjoint hdisjQ]; omega
  · exact (memS v₀).mpr hv₀S
  · intro v hv
    rw [memS]
    by_cases h0 : r = 0
    · have : v = v₀ := (((hconn v).dist_eq_zero_iff).mp (by omega)).symm
      rw [this]; exact hv₀S
    · left; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]; omega
  · intro v hv; exact hle v ((memS v).mp hv)
  · exact ⟨q, (memS q).mpr (Or.inr hq), hqr⟩
  · intro v hv hne
    obtain ⟨u, hu, hdu⟩ := h42_pred (hconn v) hne
    have hvr := hle v ((memS v).mp hv)
    refine ⟨u, (memS u).mpr (Or.inl ?_), hu, hdu⟩
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]; omega


