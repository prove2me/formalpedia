-- Prove2me | solution 1 for ECDLP.pohlig_hellman
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:04:18.926212+00:00
-- url     : https://prove2.me/submissions/a9e68aeb-8267-4c56-81bd-bb71883bc2e5

import Mathlib

namespace ECDLP

theorem pohlig_hellman {G : Type*} [AddCommGroup G] {P Q : G} {n : ℕ} (hn : 0 < n)
    (hP : addOrderOf P = n) {x : ℕ} (hQ : Q = x • P) {m : ℕ} (hm : m ∣ n) :
    addOrderOf ((n / m) • P) = m ∧ (n / m) • Q = (x % m) • ((n / m) • P) := by
  have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hm hn
  have hk0 : n / m ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn hm) hm0).ne'
  have hord : addOrderOf ((n / m) • P) = m := by
    rw [addOrderOf_nsmul_of_dvd hk0 (by rw [hP]; exact Nat.div_dvd_of_dvd hm), hP, Nat.div_div_self hm hn.ne']
  refine ⟨hord, ?_⟩
  rw [hQ, ← mul_nsmul', mul_nsmul]
  have := mod_addOrderOf_nsmul ((n / m) • P) x
  rw [hord] at this
  exact this.symm
end ECDLP

theorem solution {G : Type*} [AddCommGroup G] {P Q : G} {n : ℕ} (hn : 0 < n)
    (hP : addOrderOf P = n) {x : ℕ} (hQ : Q = x • P) {m : ℕ} (hm : m ∣ n) :
    addOrderOf ((n / m) • P) = m ∧ (n / m) • Q = (x % m) • ((n / m) • P) :=
  ECDLP.pohlig_hellman hn hP hQ hm
