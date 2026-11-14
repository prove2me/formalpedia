-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.coin_first_return_and_cost
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:22:32.663014+00:00
-- url     : https://prove2.me/submissions/6bd63203-2bab-4f72-aba9-b86469da211d

import Definitions.Def_CountingLLL_ReciprocalTest
set_option autoImplicit false
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

private theorem prefix_phase (ω : Entropy) (n t : ℕ)
    (h : ∀ k < n, ω.1 k = false ∧ ω.2.1 k = false) (ht : t ≤ 2*n) :
    ((step ω)^[t] (coinState 0)).phase = .coinOracle .initial ∨
      ((step ω)^[t] (coinState 0)).phase = .coinFair .initial := by
  let k := t/2
  have hk : k ≤ n := by dsimp [k]; omega
  have hp : ∀ q < k, ω.1 q = false ∧ ω.2.1 q = false := by
    intro q hq; exact h q (by omega)
  have hf := coin_prefix ω k hp
  by_cases ht_even : t % 2 = 0
  · have heq : t = 2*k := by dsimp [k]; omega
    rw [heq, hf]
    exact Or.inl rfl
  · have heq : t = 2*k+1 := by dsimp [k]; omega
    have hklt : k < n := by omega
    rw [heq, Function.iterate_succ_apply', hf]
    have ho := (h k hklt).1
    simp [coinState, step, ho]

private theorem coin_first_return_and_cost (ω : Entropy) (n : ℕ)
    (h : ∀ k < n, ω.1 k = false ∧ ω.2.1 k = false)
    (hexit : ω.1 n = true ∨ ω.2.1 n = true) :
    ∃ T, (((step ω)^[T] (coinState 0)).phase = .initialCheck ∨
           ((step ω)^[T] (coinState 0)).phase = .loop) ∧
      ((step ω)^[T] (coinState 0)).oracleUsed = n+1 ∧
      ∀ t < T, ((step ω)^[t] (coinState 0)).phase ≠ .initialCheck ∧
        ((step ω)^[t] (coinState 0)).phase ≠ .loop := by
  have hpre := coin_prefix ω n h
  by_cases ho : ω.1 n = true
  · refine ⟨2*n+1, ?_, ?_, ?_⟩
    · left; rw [Function.iterate_succ_apply', hpre]; simp [coinState, step, ho, coinReturn]
    · rw [Function.iterate_succ_apply', hpre]; simp [coinState, step, ho, coinReturn]
    · intro t ht
      have hphase := prefix_phase ω n t h (by omega)
      rcases hphase with hphase | hphase <;> simp [hphase]
  · have ho' : ω.1 n = false := Bool.eq_false_iff.mpr ho
    have hf : ω.2.1 n = true := hexit.resolve_left ho
    have hmid : (step ω)^[2*n+1] (coinState 0) =
        {phase := .coinFair .initial, oracleUsed := n+1, fairUsed := n} := by
      rw [Function.iterate_succ_apply', hpre]
      simp [coinState, step, ho']
    refine ⟨2*n+2, ?_, ?_, ?_⟩
    · right; rw [show 2*n+2 = (2*n+1)+1 by omega, Function.iterate_succ_apply', hmid]
      simp [step, hf, coinReturn]
    · rw [show 2*n+2 = (2*n+1)+1 by omega, Function.iterate_succ_apply', hmid]
      simp [step, hf, coinReturn]
    · intro t ht
      by_cases ht' : t ≤ 2*n
      · have hphase := prefix_phase ω n t h ht'
        rcases hphase with hphase | hphase <;> simp [hphase]
      · have heq : t = 2*n+1 := by omega
        rw [heq, hmid]
        simp

theorem solution (ω : Entropy) (n : ℕ)
    (h : ∀ k < n, ω.1 k = false ∧ ω.2.1 k = false)
    (hexit : ω.1 n = true ∨ ω.2.1 n = true) :
    ∃ T, (((step ω)^[T] ({phase := .coinOracle .initial} : State)).phase = .initialCheck ∨
           ((step ω)^[T] ({phase := .coinOracle .initial} : State)).phase = .loop) ∧
      ((step ω)^[T] ({phase := .coinOracle .initial} : State)).oracleUsed = n+1 ∧
      ∀ t < T, ((step ω)^[t] ({phase := .coinOracle .initial} : State)).phase ≠ .initialCheck ∧
        ((step ω)^[t] ({phase := .coinOracle .initial} : State)).phase ≠ .loop := by
  simpa [coinState] using coin_first_return_and_cost ω n h hexit
