-- Prove2me | solution 1 for BroughanRH.nicolasPrimorial
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T19:17:09.22486+00:00
-- url     : https://prove2.me/submissions/c4e4cfb3-7484-4104-9555-eb31cfc988bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BroughanRH_nicolasAux
import Mathlib

open Finset

theorem solution :
    ∀ p : ℕ, p.Prime →
      let n := primorial p
      (n : ℝ) / n.totient > Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) := by
  intro p hp n
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h := BroughanRH.nicolasAux (p : ℝ) hp2
  rw [Nat.floor_natCast, Chebyshev.theta_eq_log_primorial, Nat.floor_natCast] at h
  -- the index set
  have hS : (Finset.Icc 2 p).filter Nat.Prime = Nat.primesLE p := by
    ext q; simp only [mem_filter, mem_Icc, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h2, h3⟩
    · rintro ⟨h2, h3⟩; exact ⟨⟨h3.two_le, h2⟩, h3⟩
  rw [hS] at h
  set P := ∏ q ∈ Nat.primesLE p, (1 - 1 / (q : ℝ)) with hP
  have hn0 : 0 < n := primorial_pos p
  have hPpos : 0 < P := by
    apply prod_pos; intro q hq
    have hq1 : (1 : ℝ) < q := by exact_mod_cast ((Nat.mem_primesLE.1 hq).2).one_lt
    rw [sub_pos, div_lt_one (by linarith)]; exact hq1
  -- totient formula
  have htot : ((n.totient : ℕ) : ℝ) = n * P := by
    have h1 := Nat.totient_mul_prod_primeFactors n
    rw [show n.primeFactors = Nat.primesLE p from primeFactors_primorial p] at h1
    have h1r : ((n.totient : ℕ) : ℝ) * ∏ q ∈ Nat.primesLE p, (q : ℝ) =
        (n : ℝ) * ∏ q ∈ Nat.primesLE p, ((q : ℝ) - 1) := by
      have : (((n.totient * ∏ q ∈ Nat.primesLE p, q : ℕ)) : ℝ) =
          ((n * ∏ q ∈ Nat.primesLE p, (q - 1) : ℕ) : ℝ) := by rw [h1]
      push_cast at this
      rw [this]
      congr 1
      refine prod_congr rfl fun q hq => ?_
      have := ((Nat.mem_primesLE.1 hq).2).one_le
      push_cast [this]; ring
    have hprod : (0 : ℝ) < ∏ q ∈ Nat.primesLE p, (q : ℝ) := by
      apply prod_pos; intro q hq
      exact_mod_cast ((Nat.mem_primesLE.1 hq).2).pos
    have e : ∏ q ∈ Nat.primesLE p, ((q : ℝ) - 1) = P * ∏ q ∈ Nat.primesLE p, (q : ℝ) := by
      rw [hP, ← prod_mul_distrib]
      refine prod_congr rfl fun q hq => ?_
      have : (q : ℝ) ≠ 0 := by exact_mod_cast ((Nat.mem_primesLE.1 hq).2).ne_zero
      field_simp
    rw [e] at h1r
    have h2 : ((n.totient : ℕ) : ℝ) * ∏ q ∈ Nat.primesLE p, (q : ℝ) =
        ((n : ℝ) * P) * ∏ q ∈ Nat.primesLE p, (q : ℝ) := by rw [h1r]; ring
    exact mul_right_cancel₀ hprod.ne' h2
  show (n : ℝ) / n.totient > Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [htot, gt_iff_lt, div_mul_eq_div_div, div_self hnr.ne', lt_div_iff₀ hPpos]
  exact h
