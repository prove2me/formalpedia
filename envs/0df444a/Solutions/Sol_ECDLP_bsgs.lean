-- Prove2me | solution 1 for ECDLP.bsgs
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:10:46.201195+00:00
-- url     : https://prove2.me/submissions/1b6a75f3-b5db-4a15-9693-865191b4e544

import Mathlib

namespace ECDLP

theorem bsgs {G : Type*} [AddCommGroup G] {P Q : G} {n x : ℕ} (hn : 0 < n)
    (hP : addOrderOf P = n) (hx : x < n) (hQ : Q = x • P) :
    let m := Nat.sqrt n + 1
    ∃ i j : ℕ, i < m ∧ j < m ∧ j • P = Q - i • (m • P) := by
  intro m
  have hm : 0 < m := Nat.succ_pos _
  have hnm : n < m * m := Nat.lt_succ_sqrt n
  refine ⟨x / m, x % m, ?_, Nat.mod_lt _ hm, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul hm]; omega
  · rw [hQ, smul_smul, eq_sub_iff_add_eq, ← add_nsmul]
    congr 1
    rw [mul_comm]
    exact Nat.mod_add_div x m

end ECDLP

theorem solution {G : Type*} [AddCommGroup G] {P Q : G} {n x : ℕ} (hn : 0 < n)
    (hP : addOrderOf P = n) (hx : x < n) (hQ : Q = x • P) :
    let m := Nat.sqrt n + 1
    ∃ i j : ℕ, i < m ∧ j < m ∧ j • P = Q - i • (m • P) := by
  first
  | exact ECDLP.bsgs
  | exact ECDLP.bsgs ..
  | (apply ECDLP.bsgs <;> assumption)
