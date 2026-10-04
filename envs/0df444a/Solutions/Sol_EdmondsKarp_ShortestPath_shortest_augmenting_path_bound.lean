-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.shortest_augmenting_path_bound
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T19:46:28.190093+00:00
-- url     : https://prove2.me/submissions/b3be744f-d1f9-4a01-80fb-5443f2390ccb

import Theorems.Thm_EdmondsKarp_ShortestPath_bottleneck_count_le
import Theorems.Thm_EdmondsKarp_ShortestPath_isMaxFlow_iff_no_augPath
import Theorems.Thm_EdmondsKarp_ShortestPath_run_isFlow
import Theorems.Thm_EdmondsKarp_ShortestPath_pathEps_bounds

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsShortestRun N K f P) :
    4 * K ≤ Fintype.card V ^ 3 - Fintype.card V ∧
    ((¬ ∃ Q : List V, IsAugPath N (f K) Q) → IsMaxFlow N (f K)) := by
  classical
  refine ⟨?_, (isMaxFlow_iff_no_augPath N (f K) (run_isFlow N K f P hrun K le_rfl)).mpr⟩
  let S := (Finset.univ : Finset V).offDiag
  let B := fun (e : V × V) k =>
    IsBottleneck N (f k) (P k) e.1 e.2 ∨ IsBottleneck N (f k) (P k) e.2 e.1
  let C := fun k => S.filter (fun e => B e k)
  have hcount : ∀ k ∈ Finset.range K, 2 ≤ (C k).card := by
    intro k hk
    have hkK := Finset.mem_range.mp hk
    have hP := (hrun.2 k hkK).1.1
    obtain ⟨u, v, hb⟩ := (pathEps_bounds N (f k) (P k)
      (run_isFlow N K f P hrun k hkK.le) hP).2.2
    have hne : u ≠ v := by
      rcases hP.2.2.2 (u, v) hb.1 with h | h
      · exact N.no_loop (u, v) h.1
      · exact (N.no_loop (v, u) h.1).symm
    have huv : (u, v) ∈ C k := by
      simp only [C, S, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and]
      exact ⟨hne, Or.inl hb⟩
    have hvu : (v, u) ∈ C k := by
      simp only [C, S, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and]
      exact ⟨hne.symm, Or.inr hb⟩
    have hpair : (u, v) ≠ (v, u) := fun he => hne (Prod.mk.inj he).1
    have hsub : ({(u, v), (v, u)} : Finset (V × V)) ⊆ C k := by
      intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact huv
      · simpa only [Finset.mem_singleton.mp he] using hvu
    simpa [hpair] using Finset.card_le_card hsub
  have hlow : 2 * K ≤ ∑ k ∈ Finset.range K, (C k).card := by
    have h := Finset.sum_le_sum hcount
    simpa [Nat.mul_comm] using h
  have hswap : (∑ e ∈ S, ((Finset.range K).filter (fun k => B e k)).card) =
      ∑ k ∈ Finset.range K, (C k).card := by
    simp only [C, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hupp : 2 * (∑ e ∈ S, ((Finset.range K).filter (fun k => B e k)).card) ≤
      S.card * (Fintype.card V + 1) := by
    rw [Finset.mul_sum]
    have h := Finset.sum_le_sum (s := S) (fun e _ => bottleneck_count_le N K f P hrun e.1 e.2)
    simpa [B] using h
  rw [hswap] at hupp
  have htotal : 4 * K ≤ S.card * (Fintype.card V + 1) := by omega
  have hcard : S.card = Fintype.card V * Fintype.card V - Fintype.card V := by
    simp [S, Finset.offDiag_card]
  rw [hcard] at htotal
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨N.s⟩
  have hid : (Fintype.card V * Fintype.card V - Fintype.card V) * (Fintype.card V + 1) +
      Fintype.card V = Fintype.card V ^ 3 := by
    obtain ⟨n, he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [he]
    have hsq : (n + 1) * (n + 1) - (n + 1) = n * (n + 1) := by
      have : (n + 1) * (n + 1) = n * (n + 1) + (n + 1) := by ring
      omega
    rw [hsq]
    simp only [Nat.succ_eq_add_one]
    ring
  omega
