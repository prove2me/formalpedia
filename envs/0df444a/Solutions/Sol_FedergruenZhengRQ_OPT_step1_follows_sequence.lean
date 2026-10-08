-- Prove2me | solution 1 for FedergruenZhengRQ.OPT.step1_follows_sequence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T02:52:45.780277+00:00
-- url     : https://prove2.me/submissions/98309e94-b299-4207-b3fc-15817065e509

import Mathlib
import Definitions.Def_FedergruenZhengRQ_OPT_Model

open FedergruenZhengRQ.OPT in
theorem solution (κ : ℝ) (G : ℤ → ℝ) (y₁ : ℤ) :
    optInit κ G y₁ = stateAt κ G y₁ 1 ∧
    ∀ Q : ℕ, 1 ≤ Q →
      optStep G (stateAt κ G y₁ Q) =
        if Cstar κ G y₁ Q ≤ G (y G y₁ (Q + 1)) then Sum.inl (L G y₁ Q - 1, Q)
        else Sum.inr (stateAt κ G y₁ (Q + 1)) := by
  constructor
  · simp [optInit, stateAt, Cstar, y, L, R, window]
  · intro Q hQ
    obtain ⟨n, rfl⟩ : ∃ n, Q = n + 1 := ⟨Q - 1, by omega⟩
    have hLn : L G y₁ (n + 1) = (window G y₁ n).1 := by simp [L]
    have hRn : R G y₁ (n + 1) = (window G y₁ n).2 := by simp [R]
    have hL2 : L G y₁ (n + 1 + 1) = (window G y₁ (n + 1)).1 := by simp [L]
    have hR2 : R G y₁ (n + 1 + 1) = (window G y₁ (n + 1)).2 := by simp [R]
    have hy : y G y₁ (n + 1 + 1) =
        if G (L G y₁ (n + 1) - 1) ≤ G (R G y₁ (n + 1) + 1) then L G y₁ (n + 1) - 1
        else R G y₁ (n + 1) + 1 := rfl
    have hsum : ∑ i ∈ Finset.Icc 1 (n + 1 + 1), G (y G y₁ i)
        = ∑ i ∈ Finset.Icc 1 (n + 1), G (y G y₁ i) + G (y G y₁ (n + 1 + 1)) :=
      Finset.sum_Icc_succ_top (by omega) _
    have hw : window G y₁ (n + 1) =
        if G ((window G y₁ n).1 - 1) ≤ G ((window G y₁ n).2 + 1) then
          ((window G y₁ n).1 - 1, (window G y₁ n).2)
        else ((window G y₁ n).1, (window G y₁ n).2 + 1) := rfl
    unfold optStep stateAt Cstar
    simp only [hsum, hL2, hR2, hy, hw, hLn, hRn]
    by_cases h1 : G ((window G y₁ n).1 - 1) ≤ G ((window G y₁ n).2 + 1)
    · simp only [h1, if_true]
      split_ifs <;> simp [add_assoc]
    · simp only [h1, if_false]
      split_ifs <;> simp [add_assoc]
