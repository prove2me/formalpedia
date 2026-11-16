-- Prove2me | solution 1 for DirKECC1549.Asm.big_K
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-16T05:27:35.337995+00:00
-- url     : https://prove2.me/submissions/c1a8473a-41be-475f-a7cc-b64cbad14d34

import Definitions.Def_DirKECC1549_Impl_DMath

set_option autoImplicit false

section
set_option autoImplicit false

open Finset

namespace DirKECC1549.Asm

open DirKECC1549.Main

theorem bernoulli_nat (a K : ℕ) : a ^ K + K * a ^ (K - 1) ≤ (a + 1) ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [pow_succ (a + 1)]
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp
    · have e1 : a ^ (K + 1) = a ^ K * a := pow_succ a K
      have e2 : a ^ K = a ^ (K - 1) * a := by rw [← pow_succ]; congr 1; omega
      simp only [Nat.add_sub_cancel]
      nlinarith [Nat.zero_le (a ^ (K - 1)), Nat.zero_le a]

end DirKECC1549.Asm
end

set_option autoImplicit false
open Finset
open DirKECC1549.Main
open DirKECC1549 DirKECC1549.Asm

theorem solution (n m K d : ℕ) (hK : n * m < K) (hd : d < m) : n * d ^ K < m ^ K := by
  have h1 : n * d ^ K ≤ n * (m - 1) ^ K := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have h2 := bernoulli_nat (m - 1) K
  rw [show m - 1 + 1 = m by omega] at h2
  rcases Nat.eq_zero_or_pos (m - 1) with ha | ha
  · rw [ha, zero_pow (by omega)] at h1
    have : 0 < m ^ K := pow_pos (by omega) K
    omega
  · have e : (m - 1) ^ K = (m - 1) ^ (K - 1) * (m - 1) := by rw [← pow_succ]; congr 1; omega
    have hp : 0 < (m - 1) ^ (K - 1) := by positivity
    have : n * (m - 1) < (m - 1) + K := by
      have : n * (m - 1) ≤ n * m := Nat.mul_le_mul_left _ (by omega)
      omega
    have : n * (m - 1) ^ K < (m - 1) ^ K + K * (m - 1) ^ (K - 1) := by
      rw [e]; nlinarith
    omega
