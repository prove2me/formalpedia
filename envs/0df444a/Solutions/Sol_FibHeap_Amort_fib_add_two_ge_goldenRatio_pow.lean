-- Prove2me | solution 1 for FibHeap.Amort.fib_add_two_ge_goldenRatio_pow
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:51:48.79059+00:00
-- url     : https://prove2.me/submissions/71ce66be-f784-44ce-8d27-aa5be449df6b

import Mathlib



namespace FibHeap.Amort

theorem fibphi_core (k : ℕ) :
    Real.goldenRatio ^ k ≤ (Nat.fib (k + 2) : ℝ) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp
    | 1 =>
      have := Real.goldenRatio_lt_two
      simp [Nat.fib_add_two]
      linarith
    | k + 2 =>
      have h1 := ih k (by omega)
      have h2 := ih (k+1) (by omega)
      have e : Nat.fib (k + 2 + 2) = Nat.fib (k+2) + Nat.fib (k+1+2) := by
        rw [show k + 2 + 2 = (k+2) + 2 from rfl, Nat.fib_add_two]
      rw [e]; push_cast
      have : Real.goldenRatio ^ (k+2) = Real.goldenRatio ^ k + Real.goldenRatio ^ (k+1) := by
        have := Real.goldenRatio_sq
        calc Real.goldenRatio ^ (k+2)
            = Real.goldenRatio ^ k * (Real.goldenRatio^2) := by ring
          _ = _ := by rw [this]; ring
      linarith

end FibHeap.Amort

open FibHeap.Amort


theorem solution (k : ℕ) :
    Real.goldenRatio ^ k ≤ (Nat.fib (k + 2) : ℝ) := by
  exact fibphi_core k
