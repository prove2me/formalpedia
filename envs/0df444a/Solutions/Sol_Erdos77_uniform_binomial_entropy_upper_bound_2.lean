-- Prove2me | solution 2 for Erdos77.uniform_binomial_entropy_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T16:24:05.162135+00:00
-- url     : https://prove2.me/submissions/3519ff26-c8e2-4a14-b083-4438913b4e7d

import Mathlib
open Filter Topology

theorem solution :
  forall k ell : Nat, 0 < k -> 0 < ell -> ell <= k ->
    (Nat.choose (k + ell) ell : Real) <=
      Real.exp (((1 + ((ell : Real) / k)) * Real.log (1 + ((ell : Real) / k)) -
        ((ell : Real) / k) * Real.log ((ell : Real) / k)) * (k : Real)) := by
  intro k ell hk hell hle
  let n : Nat := k + ell
  let p : Real := (ell : Real) / (n : Real)
  let q : Real := (k : Real) / (n : Real)
  have hn : (0 : Real) < n := by
    dsimp [n]
    positivity
  have hp : 0 < p := by
    dsimp [p]
    positivity
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hpq : p + q = 1 := by
    dsimp [p, q, n]
    have hkpos : (0 : Real) < (k : Real) := by exact_mod_cast hk
    have hellpos : (0 : Real) < (ell : Real) := by exact_mod_cast hell
    field_simp
    <;> push_cast
    <;> ring
  have hsum : (∑ i ∈ Finset.range (n + 1),
      p ^ i * q ^ (n - i) * (Nat.choose n i : Real)) = 1 := by
    rw [← add_pow]
    simp [hpq]
  have hterm : p ^ ell * q ^ k * (Nat.choose n ell : Real) ≤ 1 := by
    have hle_sum := Finset.single_le_sum
      (s := Finset.range (n + 1))
      (f := fun i => p ^ i * q ^ (n - i) * (Nat.choose n i : Real))
      (by
        intro i hi
        positivity)
      (show ell ∈ Finset.range (n + 1) by
        apply Finset.mem_range.mpr
        dsimp [n]
        omega)
    have hnsub : n - ell = k := by dsimp [n]; omega
    simpa [hnsub] using hle_sum.trans_eq hsum
  have hfac : 0 < p ^ ell * q ^ k := by positivity
  have hchoose : (Nat.choose n ell : Real) ≤ 1 / (p ^ ell * q ^ k) := by
    rw [le_div_iff₀ hfac]
    nlinarith [hterm]
  have hlog : Real.log (1 / (p ^ ell * q ^ k)) =
      -((ell : Real) * Real.log p + (k : Real) * Real.log q) := by
    rw [one_div, Real.log_inv, Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
  have htarget :
      -((ell : Real) * Real.log p + (k : Real) * Real.log q) =
      (((1 + ((ell : Real) / k)) * Real.log (1 + ((ell : Real) / k)) -
        ((ell : Real) / k) * Real.log ((ell : Real) / k)) * (k : Real)) := by
    dsimp [p, q, n]
    push_cast
    have hkpos : (0 : Real) < (k : Real) := by exact_mod_cast hk
    have hellpos : (0 : Real) < (ell : Real) := by exact_mod_cast hell
    have hsumarg : (1 + (ell : Real) / (k : Real)) = ((k : Real) + ell) / k := by
      field_simp
      <;> ring
    have h1 : Real.log (1 + (ell : Real) / (k : Real)) =
        Real.log ((k : Real) + ell) - Real.log (k : Real) := by
      rw [hsumarg, Real.log_div (by positivity) (by positivity)]
    have h2 : Real.log ((ell : Real) / (k : Real)) =
        Real.log (ell : Real) - Real.log (k : Real) := by
      rw [Real.log_div (by positivity) (by positivity)]
    have h3 : Real.log ((ell : Real) / ((k : Real) + ell)) =
        Real.log (ell : Real) - Real.log ((k : Real) + ell) := by
      rw [Real.log_div (by positivity) (by positivity)]
    have h4 : Real.log ((k : Real) / ((k : Real) + ell)) =
        Real.log (k : Real) - Real.log ((k : Real) + ell) := by
      rw [Real.log_div (by positivity) (by positivity)]
    rw [h1, h2, h3, h4]
    push_cast
    field_simp
    ring
  have hbound : Real.exp (Real.log (Nat.choose n ell : Real)) ≤
      Real.exp (Real.log (1 / (p ^ ell * q ^ k))) := by
    apply Real.exp_le_exp.mpr
    exact Real.log_le_log (by exact_mod_cast Nat.choose_pos (by dsimp [n]; omega)) hchoose
  have hchoose_eq : Real.exp (Real.log (Nat.choose n ell : Real)) =
      (Nat.choose n ell : Real) := by
    rw [Real.exp_log]
    exact_mod_cast Nat.choose_pos (by dsimp [n]; omega)
  calc
    (Nat.choose (k + ell) ell : Real) = (Nat.choose n ell : Real) := by rfl
    _ ≤ Real.exp (Real.log (1 / (p ^ ell * q ^ k))) := by
      rw [← hchoose_eq]
      exact hbound
    _ = Real.exp (((1 + ((ell : Real) / k)) * Real.log (1 + ((ell : Real) / k)) -
        ((ell : Real) / k) * Real.log ((ell : Real) / k)) * (k : Real)) := by
      rw [hlog, htarget]
