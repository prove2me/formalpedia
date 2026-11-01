-- Prove2me | solution 1 for ExpConMinimax.lemma_22
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T14:05:11.675763+00:00
-- url     : https://prove2.me/submissions/4864fd80-5d21-4e7b-8c5a-621aa5a124b1

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

private lemma expcon_aux (a : ℕ → ℝ) (b₁ b₂ : ℝ) (_ha : ∀ t, 0 ≤ a t) (_hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (ha₀ : a 0 ≤ b₁)
    (hrec : ∀ K, 1 ≤ K → a K ≤ b₁ + b₂ * ∑ t ∈ Finset.range K, a t) :
    ∀ K : ℕ, a K ≤ b₁ * (1 + b₂) ^ K := by
  intro K
  induction K using Nat.strong_induction_on with
  | h K ih =>
    rcases K with _ | K
    · simpa using ha₀
    · have hK1 : 1 ≤ K + 1 := Nat.succ_pos K
      have hstep := hrec (K + 1) hK1
      have hsum : ∑ t ∈ Finset.range (K + 1), a t ≤ ∑ t ∈ Finset.range (K + 1), b₁ * (1 + b₂) ^ t := by
        exact Finset.sum_le_sum (fun t ht => ih t (Finset.mem_range.mp ht))
      have hgeom : b₁ + b₂ * ∑ t ∈ Finset.range (K + 1), b₁ * (1 + b₂) ^ t = b₁ * (1 + b₂) ^ (K + 1) := by
        clear hstep hsum ih hrec ha₀ _ha hK1
        induction K with
        | zero => simp; ring
        | succ m ihm =>
          rw [Finset.sum_range_succ, mul_add, ← add_assoc, ihm]
          ring
      nlinarith

theorem solution (a : ℕ → ℝ) (b₁ b₂ : ℝ) (ha : ∀ t, 0 ≤ a t) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (ha₀ : a 0 ≤ b₁)
    (hrec : ∀ K, 1 ≤ K → a K ≤ b₁ + b₂ * ∑ t ∈ Finset.range K, a t) :
    ∀ K, 1 ≤ K → a K ≤ b₁ * (1 + b₂) ^ K := by
  intro K _
  exact expcon_aux a b₁ b₂ ha hb₁ hb₂ ha₀ hrec K
