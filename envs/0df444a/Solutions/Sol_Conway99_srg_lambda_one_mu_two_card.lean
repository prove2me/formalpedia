-- Prove2me | solution 1 for Conway99.srg_lambda_one_mu_two_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-06T16:52:14.086344+00:00
-- url     : https://prove2.me/submissions/290c0fe3-0f2a-436d-bb88-84a8f9cdfc18

import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

open SimpleGraph Finset

theorem solution {V : Type*} [Fintype V] {g : SimpleGraph V}
    [DecidableRel g.Adj] {n k : ℕ} (h : g.IsSRGWith n k 1 2) (hn : 0 < n) :
    2 * n = k ^ 2 + 2 := by
  classical
  have hcard : Fintype.card V = n := h.card
  have hne : Nonempty V := by
    rw [← Fintype.card_pos_iff, hcard]; exact hn
  obtain ⟨v⟩ := hne
  have hdeg : g.degree v = k := h.regular v
  -- `k + 1 ≤ n` : the neighbourhood of `v` misses `v` itself
  have hkle : k + 1 ≤ n := by
    have hsub : g.neighborFinset v ⊆ Finset.univ.erase v := by
      intro w hw
      rw [mem_neighborFinset] at hw
      exact Finset.mem_erase.2 ⟨(g.ne_of_adj hw).symm, Finset.mem_univ _⟩
    have hcle := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hcard] at hcle
    have : g.degree v = (g.neighborFinset v).card := rfl
    omega
  -- `λ = 1` forces every vertex of positive degree to have degree at least two
  have hk2 : k = 0 ∨ 2 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · exact Or.inl h0
    refine Or.inr ?_
    have hnb : (g.neighborFinset v).Nonempty := by
      rw [← Finset.card_pos]
      have : (g.neighborFinset v).card = k := hdeg
      omega
    obtain ⟨w, hw⟩ := hnb
    rw [mem_neighborFinset] at hw
    have hcn : Fintype.card (g.commonNeighbors v w) = 1 := h.of_adj v w hw
    have hnn : Nonempty (g.commonNeighbors v w) := by
      rw [← Fintype.card_pos_iff, hcn]; norm_num
    obtain ⟨u, hu⟩ := hnn
    have hu1 : g.Adj v u := hu.1
    have hu2 : g.Adj w u := hu.2
    have hwu : w ≠ u := g.ne_of_adj hu2
    have hsub : ({w, u} : Finset V) ⊆ g.neighborFinset v := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (mem_neighborFinset _ _ _).2 hw
      · exact (mem_neighborFinset _ _ _).2 hu1
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simpa using hwu), Finset.card_singleton] at this
    have hd : (g.neighborFinset v).card = k := hdeg
    omega
  have hpar := SimpleGraph.IsSRGWith.param_eq g h hn
  rcases hk2 with rfl | hk2
  · simp only [Nat.zero_sub, Nat.zero_mul, Nat.sub_zero] at hpar
    have : n - 1 = 0 := by omega
    have hn1 : n = 1 := by omega
    subst hn1; norm_num
  · obtain ⟨a, rfl⟩ : ∃ a, k = a + 2 := ⟨k - 2, by omega⟩
    obtain ⟨c, rfl⟩ : ∃ c, n = c + (a + 2) + 1 := ⟨n - (a + 2) - 1, by omega⟩
    have e1 : a + 2 - 1 - 1 = a := by omega
    have e2 : c + (a + 2) + 1 - (a + 2) - 1 = c := by omega
    rw [e1, e2] at hpar
    nlinarith [hpar]
