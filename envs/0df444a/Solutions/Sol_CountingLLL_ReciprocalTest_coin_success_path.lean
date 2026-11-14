-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.coin_success_path
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:57:35.248193+00:00
-- url     : https://prove2.me/submissions/fcf256c4-6f46-43d4-8f7b-f1c09fb51b58

import Definitions.Def_CountingLLL_ReciprocalTest

open CountingLLL.ReciprocalTest

private def coinState (n : ℕ) : State := { phase := .coinOracle .initial, oracleUsed := n, fairUsed := n }

private theorem coin_continue (ω : Entropy) (n : ℕ) (ho : ω.1 n = false) (hf : ω.2.1 n = false) :
    (step ω)^[2] (coinState n) = coinState (n+1) := by
  simp [coinState, step, Function.iterate_succ_apply', ho, hf]

private theorem coin_prefix (ω : Entropy) (n : ℕ)
    (h : ∀ k < n, ω.1 k = false ∧ ω.2.1 k = false) :
    (step ω)^[2*n] (coinState 0) = coinState n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := h n (Nat.lt_succ_self n)
    have hprev : ∀ k < n, ω.1 k = false ∧ ω.2.1 k = false := by
      intro k hk; exact h k (Nat.lt.step hk)
    have hi := ih hprev
    rw [show 2 * (n + 1) = 2 + 2 * n by omega, Function.iterate_add_apply, hi]
    exact coin_continue ω n hn.1 hn.2

private theorem coin_one_path (ω : Entropy) (n : ℕ)
    (h : ∀ k < n, ω.1 k = false ∧ ω.2.1 k = false) (ho : ω.1 n = true) :
    ((step ω)^[2*n+1] (coinState 0)).phase = .initialCheck := by
  rw [Function.iterate_succ_apply', coin_prefix ω n h]
  simp [coinState, step, ho, coinReturn]


theorem solution (ω : Entropy) (n : ℕ) (h : ∀ k < n, ω.1 k = false ∧ ω.2.1 k = false) (ho : ω.1 n = true) : ((step ω)^[2*n+1] ({phase := .coinOracle .initial} : State)).phase = .initialCheck := by
  simpa [coinState] using coin_one_path ω n h ho
