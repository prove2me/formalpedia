-- Prove2me | solution 1 for BehrendWindows.relation_of_map_relation
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-21T01:56:11.856461+00:00
-- url     : https://prove2.me/submissions/2dd93f37-1811-44ce-a403-9cc2eb653f51

import Mathlib

theorem solution {n : ℕ} (d m p q : ℕ) (x y z : Fin n → ℕ)
    (hx : ∀ i, x i < d) (hy : ∀ i, y i < d) (hz : ∀ i, z i < d)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : p + q < m)
    (h : p * Behrend.map (m * d) x + q * Behrend.map (m * d) z = (p + q) * Behrend.map (m * d) y) :
    p • x + q • z = (p + q) • y := by
  have hpd : ∀ w : ℕ, w < d → p * w < p * d := fun w hw => Nat.mul_lt_mul_of_pos_left hw (by omega)
  have hqd : ∀ w : ℕ, w < d → q * w ≤ q * d := fun w hw => Nat.mul_le_mul_left q hw.le
  have hmd : (p + q) * d ≤ m * d := Nat.mul_le_mul_right d hpq.le
  apply Behrend.map_injOn (d := m * d)
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hpd _ (hx i); have := hqd _ (hz i)
    nlinarith
  · intro i
    simp only [Pi.smul_apply, smul_eq_mul]
    have : (p + q) * y i < (p + q) * d := Nat.mul_lt_mul_of_pos_left (hy i) (by omega)
    omega
  · simp only [map_add, map_nsmul, smul_eq_mul]
    exact h
