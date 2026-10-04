-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.card_le_of_gap_two
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T20:16:04.486817+00:00
-- url     : https://prove2.me/submissions/a2372def-6986-4955-9e16-4d3fbd9e0b96

import Mathlib

theorem solution (S : Finset ℕ) (d : ℕ → ℕ) (n : ℕ)
    (hbound : ∀ k ∈ S, d k < n)
    (hgap : ∀ k ∈ S, ∀ l ∈ S, k < l → d k + 2 ≤ d l) :
    2 * S.card ≤ n + 1 := by
  have hind : ∀ i (hi : i < S.card), 2 * i ≤ d (S.orderEmbOfFin rfl ⟨i, hi⟩) := by
    intro i
    induction i with
    | zero => intro hi; omega
    | succ i ih =>
      intro hi
      have hi' : i < S.card := by omega
      have hp := ih hi'
      have hg := hgap _ (S.orderEmbOfFin_mem rfl ⟨i, hi'⟩)
        _ (S.orderEmbOfFin_mem rfl ⟨i + 1, hi⟩)
        ((S.orderEmbOfFin rfl).strictMono (show (⟨i, hi'⟩ : Fin S.card) < ⟨i + 1, hi⟩ from Nat.lt_succ_self i))
      omega
  by_cases hz : S.card = 0
  · simp [hz]
  · have hi : S.card - 1 < S.card := by omega
    have hp := hind (S.card - 1) hi
    have hb := hbound _ (S.orderEmbOfFin_mem rfl ⟨S.card - 1, hi⟩)
    omega
