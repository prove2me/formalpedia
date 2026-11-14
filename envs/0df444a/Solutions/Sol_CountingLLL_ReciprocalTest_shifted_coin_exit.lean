-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.shifted_coin_exit
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:31:44.408203+00:00
-- url     : https://prove2.me/submissions/d533d775-bf7b-41f8-82aa-22e5505d01e7

import Definitions.Def_CountingLLL_ReciprocalTest
set_option autoImplicit false
open CountingLLL.ReciprocalTest

private def seed (s : State) (ctx : Context) (n : ℕ) : State :=
  {s with phase := .coinOracle ctx, oracleUsed := s.oracleUsed+n, fairUsed := s.fairUsed+n}

private theorem coin_continue_shifted (ω : Entropy) (s : State) (ctx : Context) (n : ℕ)
    (ho : ω.1 (s.oracleUsed+n) = false) (hf : ω.2.1 (s.fairUsed+n) = false) :
    (step ω)^[2] (seed s ctx n) = seed s ctx (n+1) := by
  simp [seed, step, Function.iterate_succ_apply', ho, hf, Nat.add_assoc]

private theorem coin_prefix_shifted (ω : Entropy) (s : State) (ctx : Context) (n : ℕ)
    (h : ∀ k < n, ω.1 (s.oracleUsed+k) = false ∧ ω.2.1 (s.fairUsed+k) = false) :
    (step ω)^[2*n] (seed s ctx 0) = seed s ctx n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := h n (Nat.lt_succ_self n)
    have hprev : ∀ k < n, ω.1 (s.oracleUsed+k) = false ∧ ω.2.1 (s.fairUsed+k) = false := by
      intro k hk; exact h k (Nat.lt_succ_of_lt hk)
    rw [show 2*(n+1) = 2+2*n by omega, Function.iterate_add_apply, ih hprev]
    exact coin_continue_shifted ω s ctx n hn.1 hn.2

/-- The local Coin trace works from arbitrary counters and all call sites. -/
private theorem shifted_coin_exit (ω : Entropy) (s : State) (ctx : Context) (n : ℕ)
    (h : ∀ k < n, ω.1 (s.oracleUsed+k) = false ∧ ω.2.1 (s.fairUsed+k) = false) :
    (ω.1 (s.oracleUsed+n) = true →
      (step ω)^[2*n+1] (seed s ctx 0) =
        coinReturn ctx true {seed s ctx n with oracleUsed := s.oracleUsed+n+1}) ∧
    (ω.1 (s.oracleUsed+n) = false → ω.2.1 (s.fairUsed+n) = true →
      (step ω)^[2*n+2] (seed s ctx 0) =
        coinReturn ctx false {seed s ctx n with oracleUsed := s.oracleUsed+n+1, fairUsed := s.fairUsed+n+1}) := by
  constructor
  · intro ho
    rw [Function.iterate_succ_apply', coin_prefix_shifted ω s ctx n h]
    simp [step, seed, ho]
  · intro ho hf
    rw [show 2*n+2 = (2*n+1)+1 by omega, Function.iterate_succ_apply',
      Function.iterate_succ_apply', coin_prefix_shifted ω s ctx n h]
    simp [step, seed, ho, hf]
    cases ctx <;> simp [coinReturn]

theorem solution (ω : Entropy) (s : State) (ctx : Context) (n : ℕ)
    (h : ∀ k < n, ω.1 (s.oracleUsed+k) = false ∧ ω.2.1 (s.fairUsed+k) = false) :
    (ω.1 (s.oracleUsed+n) = true →
      (step ω)^[2*n+1] ({s with phase := .coinOracle ctx} : State) =
        coinReturn ctx true {s with phase := .coinOracle ctx, oracleUsed := s.oracleUsed+n+1, fairUsed := s.fairUsed+n}) ∧
    (ω.1 (s.oracleUsed+n) = false → ω.2.1 (s.fairUsed+n) = true →
      (step ω)^[2*n+2] ({s with phase := .coinOracle ctx} : State) =
        coinReturn ctx false {s with phase := .coinOracle ctx, oracleUsed := s.oracleUsed+n+1, fairUsed := s.fairUsed+n+1}) := by
  simpa [seed] using shifted_coin_exit ω s ctx n h
