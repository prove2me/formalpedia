-- Prove2me | solution 1 for Erdos287.short_cofactor_cycles_balance
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T13:46:30.489168+00:00
-- url     : https://prove2.me/submissions/76c76692-2006-44c4-9d30-1bc7f52e799e

import Mathlib

open Finset

set_option autoImplicit false

/-- Along a sufficiently short cycle of adjacent multiples, the products of
the outgoing and incoming cofactors agree. -/
theorem solution (a b p : ℕ → ℕ) (k B : ℕ) (hk : 0 < k)
    (hclose : p k = p 0) (hsize : k * B ^ (k - 1) < p 0)
    (hab : ∀ i < k, a i ≤ B ∧ b i ≤ B)
    (hstep : ∀ i < k, |(a i : ℤ) * p i - (b i : ℤ) * p (i + 1)| = 1) :
    (∏ i ∈ Finset.range k, a i) = ∏ i ∈ Finset.range k, b i := by
  let A (n : ℕ) := ∏ i ∈ range n, a i
  let C (n : ℕ) := ∏ i ∈ range n, b i
  let E (n : ℕ) := (A n : ℤ) * p 0 - (C n : ℤ) * p n
  have hC (n : ℕ) (hn : n ≤ k) : C n ≤ B ^ n := by
    calc
      C n ≤ ∏ _ ∈ range n, B := prod_le_prod' fun i hi => (hab i ((mem_range.mp hi).trans_le hn)).2
      _ = _ := by simp
  have hrecur (n : ℕ) :
      E (n + 1) = (a n : ℤ) * E n +
        (C n : ℤ) * ((a n : ℤ) * p n - (b n : ℤ) * p (n + 1)) := by
    simp only [E, A, C, prod_range_succ, Nat.cast_mul]
    ring
  have hE (n : ℕ) (hn : n < k) : |E (n + 1)| ≤ (↑(n + 1) : ℤ) * (B : ℤ) ^ n := by
    induction n with
    | zero =>
      simpa [E, A, C] using (hstep 0 hk).le
    | succ n ih =>
      have hn' : n < k := Nat.lt_of_succ_lt hn
      have ha : (a (n + 1) : ℤ) ≤ B := by exact_mod_cast (hab (n + 1) hn).1
      have hc : (C (n + 1) : ℤ) ≤ (B : ℤ) ^ (n + 1) := by
        exact_mod_cast hC (n + 1) hn.le
      rw [hrecur (n + 1)]
      calc
        _ ≤ |(a (n + 1) : ℤ) * E (n + 1)| +
            |(C (n + 1) : ℤ) * ((a (n + 1) : ℤ) * p (n + 1) -
              (b (n + 1) : ℤ) * p (n + 1 + 1))| := abs_add_le _ _
        _ ≤ (B : ℤ) * ((↑(n + 1) : ℤ) * (B : ℤ) ^ n) + (B : ℤ) ^ (n + 1) := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ a (n + 1)),
            abs_of_nonneg (by positivity : (0 : ℤ) ≤ C (n + 1)), hstep (n + 1) hn, mul_one]
          exact add_le_add (mul_le_mul ha (ih hn') (abs_nonneg _) (by positivity)) hc
        _ = _ := by push_cast; rw [pow_succ]; ring
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hE' := hE (k - 1) (Nat.sub_lt hk (by decide))
  rw [hk'] at hE'
  have hlt : |E k| < (p 0 : ℤ) := hE'.trans_lt (by exact_mod_cast hsize)
  have hEk : E k = ((A k : ℤ) - (C k : ℤ)) * p 0 := by
    dsimp [E]
    rw [hclose, sub_mul]
  by_contra hneq
  have hne : (A k : ℤ) - (C k : ℤ) ≠ 0 := by
    intro h
    apply hneq
    exact_mod_cast sub_eq_zero.mp h
  have hone : (1 : ℤ) ≤ |(A k : ℤ) - (C k : ℤ)| := by
    have hp := abs_pos.mpr hne
    omega
  rw [hEk, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ p 0)] at hlt
  have hlow := mul_le_mul_of_nonneg_right hone (by positivity : (0 : ℤ) ≤ p 0)
  rw [one_mul] at hlow
  exact hlt.not_ge hlow

