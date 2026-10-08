-- Prove2me | solution 1 for CollatzFrontier.syracuse_terminal_budget_of_descent
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-04T18:22:17.689984+00:00
-- url     : https://prove2.me/submissions/3d576559-01a2-4a9b-ac1f-27adb95946bb

import Definitions.Def_syracuseStep
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith

/-
Self-contained solution. Helper lemmas are adapted (and renamed under
`CollatzFrontierAux` to avoid any clash) from the private repo
`collatz-frontier` (commit 4d656b9c9c5815305bd391f206c9d3e9587dd395),
files `lean/CollatzFrontier/AffineStep.lean`, `TerminalBudget.lean`,
`AffineDrift.lean`. No repo module is imported.

Proof architecture. Write `S i = ∑_{j<i} a j`. The budget hypothesis gives
`S k + e ≤ K`, and descent `B < b 0` forces the contraction `3^(k+1) < 2^(S k + e)`.
* If `0 < e` or `S k < K`, every intermediate coefficient `3^i 2^(K - S i)`
  (`1 ≤ i ≤ k`) is even, so the orbit of `r + 2^K q` is exactly affine for `k`
  steps and the terminal row bounds step `k + 1`.
* If `e = 0` and `S k = K`, the coefficient at step `k` is the odd number `3^k`,
  so step `k` is only known up to its odd part `y`; one more step from the odd
  `y` divides by at least `2`, and `3^(k+1) < 2^K` closes the bound.
-/

namespace CollatzFrontierAux

/-- A power-of-two factor supplies an upper bound without fixing the valuation. -/
theorem syracuseStep_le_of_pow_two_factor {x y e : ℕ}
    (h : 3 * x + 1 = 2 ^ e * y) : syracuseStep x ≤ y := by
  unfold syracuseStep
  rw [h, Nat.ordCompl_self_pow_mul y e Nat.prime_two]
  exact Nat.ordCompl_le y 2

/-- Exact affine transfer; oddness is required only for an exact step. -/
theorem syracuseStep_affine (e : ℕ) {b A c D q : ℕ}
    (hc : 3 * b + 1 = 2 ^ e * c)
    (hD : 3 * A = 2 ^ e * D)
    (hodd : ¬ 2 ∣ c + D * q) :
    syracuseStep (b + A * q) = c + D * q := by
  unfold syracuseStep
  have h : 3 * (b + A * q) + 1 = 2 ^ e * (c + D * q) := by
    calc
      3 * (b + A * q) + 1 = (3 * b + 1) + (3 * A) * q := by ring
      _ = 2 ^ e * (c + D * q) := by rw [hc, hD]; ring
  rw [h]
  exact Nat.ordCompl_pow_mul_of_not_dvd e Nat.prime_two hodd

/-- Affine coefficient propagation under a finite power-of-two budget. -/
theorem coefficient_factor {K S e i : ℕ} (h : S + e ≤ K) :
    3 * (3 ^ i * 2 ^ (K - S)) =
      2 ^ e * (3 ^ (i + 1) * 2 ^ (K - (S + e))) := by
  have hs : K - S = e + (K - (S + e)) := by omega
  rw [hs, pow_add, pow_succ]
  ring

/-- Exact affine prefix. If every partial exponent sum `S (i+1)` (`i < j`) stays
strictly below `K`, then for `i ≤ j` the `i`-th Syracuse iterate of `r + 2^K q` is
exactly `b i + 3^i 2^(K - S i) q`: each intermediate coefficient is even, so the
odd quotients `b (i+1)` keep the whole affine value odd and every step is exact. -/
theorem prefix_exact (a b : ℕ → ℕ) (r K j : ℕ)
    (hstart : b 0 = r)
    (hstep : ∀ i < j, 3 * b i + 1 = 2 ^ (a i) * b (i + 1))
    (hodd : ∀ i < j, Odd (b (i + 1)))
    (hroom : ∀ i < j, (∑ t ∈ Finset.range (i + 1), a t) < K) (q : ℕ) :
    ∀ i, i ≤ j → syracuseStep^[i] (r + 2 ^ K * q) =
      b i + 3 ^ i * 2 ^ (K - ∑ t ∈ Finset.range i, a t) * q := by
  have hsucc (i : ℕ) : (∑ t ∈ Finset.range (i + 1), a t) =
      (∑ t ∈ Finset.range i, a t) + a i := Finset.sum_range_succ a i
  have hcoeff {i : ℕ} (hi : i < j) :
      3 * (3 ^ i * 2 ^ (K - ∑ t ∈ Finset.range i, a t)) =
        2 ^ (a i) * (3 ^ (i + 1) * 2 ^ (K - ∑ t ∈ Finset.range (i + 1), a t)) := by
    rw [hsucc]
    exact coefficient_factor (by have hh := hroom i hi; rw [hsucc] at hh; omega)
  have heven {i : ℕ} (hi : i < j) :
      (3 ^ (i + 1) * 2 ^ (K - ∑ t ∈ Finset.range (i + 1), a t)) % 2 = 0 := by
    have hpos : 0 < K - ∑ t ∈ Finset.range (i + 1), a t := by
      have hh := hroom i hi; omega
    have hexp : K - ∑ t ∈ Finset.range (i + 1), a t =
        (K - ∑ t ∈ Finset.range (i + 1), a t - 1) + 1 := by omega
    rw [hexp]
    simp [pow_succ, Nat.mul_mod]
  intro i
  induction i with
  | zero =>
      intro _
      simp [hstart]
  | succ i ih =>
      intro hi
      have hik : i < j := by omega
      rw [Function.iterate_succ_apply', ih (by omega)]
      apply syracuseStep_affine (a i) (hstep i hik) (hcoeff hik)
      have hc : b (i + 1) % 2 = 1 := by
        obtain ⟨u, hu⟩ := hodd i hik
        omega
      have hmod : (b (i + 1) +
          3 ^ (i + 1) * 2 ^ (K - ∑ t ∈ Finset.range (i + 1), a t) * q) % 2 = 1 := by
        rw [Nat.add_mod, Nat.mul_mod, heven hik]
        simp [hc]
      intro hdvd
      have hz := Nat.mod_eq_zero_of_dvd hdvd
      omega

/-- Source-shaped terminal-budget transfer, in the case where the budget leaves
room after the exact prefix (`0 < e` or `S k < K`). -/
theorem syracuse_terminal_budget
    (a b : ℕ → ℕ) (r K k e B : ℕ)
    (hstart : b 0 = r)
    (hstep : ∀ i < k, 3 * b i + 1 = 2 ^ (a i) * b (i + 1))
    (hodd : ∀ i < k, Odd (b (i + 1)))
    (hfinal : 3 * b k + 1 = 2 ^ e * B)
    (hbudget : (∑ i ∈ Finset.range k, a i) + e ≤ K)
    (hroom : 0 < e ∨ (∑ i ∈ Finset.range k, a i) < K)
    (hcontract : 3 ^ (k + 1) < 2 ^ ((∑ i ∈ Finset.range k, a i) + e))
    (hdesc : B < r) (q : ℕ) :
    syracuseStep^[k + 1] (r + 2 ^ K * q) < r + 2 ^ K * q := by
  have hpref := prefix_exact a b r K k hstart hstep hodd (by
    intro i hi
    have hh : (∑ t ∈ Finset.range (i + 1), a t) ≤ ∑ t ∈ Finset.range k, a t :=
      Finset.sum_le_sum_of_subset (Finset.range_mono (show i + 1 ≤ k by omega))
    omega) q k le_rfl
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ i ∈ Finset.range k, a i := ⟨_, rfl⟩
  rw [← hS] at hpref hbudget hcontract
  have hDfactor : 3 * (3 ^ k * 2 ^ (K - S)) =
      2 ^ e * (3 ^ (k + 1) * 2 ^ (K - (S + e))) := coefficient_factor hbudget
  have hbound : syracuseStep (b k + 3 ^ k * 2 ^ (K - S) * q) ≤
      B + 3 ^ (k + 1) * 2 ^ (K - (S + e)) * q := by
    apply syracuseStep_le_of_pow_two_factor (e := e)
    calc
      3 * (b k + 3 ^ k * 2 ^ (K - S) * q) + 1 =
          (3 * b k + 1) + (3 * (3 ^ k * 2 ^ (K - S))) * q := by ring
      _ = 2 ^ e * (B + 3 ^ (k + 1) * 2 ^ (K - (S + e)) * q) := by
          rw [hfinal, hDfactor]; ring
  have hDle : 3 ^ (k + 1) * 2 ^ (K - (S + e)) ≤ 2 ^ K := by
    have hlt := Nat.mul_lt_mul_of_pos_right hcontract
      (show 0 < 2 ^ (K - (S + e)) from pow_pos (by decide) _)
    have hsum : S + e + (K - (S + e)) = K := by omega
    rw [← pow_add, hsum] at hlt
    exact Nat.le_of_lt hlt
  have hmul := Nat.mul_le_mul_right q hDle
  have hgap : B + 3 ^ (k + 1) * 2 ^ (K - (S + e)) * q < r + 2 ^ K * q := by omega
  rw [Function.iterate_succ_apply', hpref]
  exact lt_of_le_of_lt hbound hgap

/-- The scaled representative orbit grows by a nonnegative affine intercept. -/
theorem dyadic_chain_growth (a b : ℕ → ℕ) (k : ℕ)
    (hstep : ∀ i < k, 3 * b i + 1 = 2 ^ (a i) * b (i + 1)) :
    3 ^ k * b 0 ≤ 2 ^ (∑ i ∈ Finset.range k, a i) * b k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hp := ih (fun i hi => hstep i (by omega))
      rw [Finset.sum_range_succ, pow_add, pow_succ]
      calc
        _ ≤ 3 * (2 ^ (∑ i ∈ Finset.range k, a i) * b k) := by nlinarith [hp]
        _ ≤ 2 ^ (∑ i ∈ Finset.range k, a i) * (3 * b k + 1) := by
          calc
            _ ≤ 3 * (2 ^ (∑ i ∈ Finset.range k, a i) * b k) +
                2 ^ (∑ i ∈ Finset.range k, a i) := Nat.le_add_right _ _
            _ = _ := by ring
        _ = _ := by rw [hstep k (by omega)]; ring

/-- A final `+1` supplies strict drift; representative descent implies contraction. -/
theorem terminal_power_contraction (a b : ℕ → ℕ) (k e B : ℕ)
    (hstep : ∀ i < k, 3 * b i + 1 = 2 ^ (a i) * b (i + 1))
    (hfinal : 3 * b k + 1 = 2 ^ e * B)
    (hdesc : B ≤ b 0) :
    3 ^ (k + 1) < 2 ^ ((∑ i ∈ Finset.range k, a i) + e) := by
  have hp := dyadic_chain_growth a b k hstep
  have hpow : 0 < 2 ^ (∑ i ∈ Finset.range k, a i) := pow_pos (by decide) _
  have hx : 3 ^ (k + 1) * b 0 <
      2 ^ ((∑ i ∈ Finset.range k, a i) + e) * b 0 := by
    calc
      _ ≤ 3 * (2 ^ (∑ i ∈ Finset.range k, a i) * b k) := by rw [pow_succ]; nlinarith
      _ < 2 ^ (∑ i ∈ Finset.range k, a i) * (3 * b k + 1) := by nlinarith
      _ = 2 ^ ((∑ i ∈ Finset.range k, a i) + e) * B := by rw [hfinal, pow_add]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ hdesc
  exact Nat.lt_of_mul_lt_mul_right hx

/-- The tight case `e = 0`, `S (m+1) = K` (with `k = m + 1`). The last exact
exponent `a m` is positive by parity, so the prefix is exact up to step `m`;
step `m + 1` lands on the odd part `y` of `x = b (m+1) + 3^(m+1) q`, and step
`m + 2` from the odd `y` is at most `(3y+1)/2 ≤ (3x+1)/2 = (B + 3^(m+2) q)/2`,
which is below `r + 2^K q` because `B < r` and `3^(m+2) < 2^K`. -/
theorem terminal_tight_case (a b : ℕ → ℕ) (r K m B : ℕ)
    (hstart : b 0 = r)
    (hstep : ∀ i < m + 1, 3 * b i + 1 = 2 ^ (a i) * b (i + 1))
    (hodd : ∀ i < m + 1, Odd (b (i + 1)))
    (hfinal : 3 * b (m + 1) + 1 = B)
    (hK : (∑ i ∈ Finset.range (m + 1), a i) = K)
    (hdesc : B < r) (q : ℕ) :
    syracuseStep^[m + 1 + 1] (r + 2 ^ K * q) < r + 2 ^ K * q := by
  -- contraction `3^(m+2) < 2^K`
  have hc : 3 ^ (m + 1 + 1) < 2 ^ K := by
    have h := terminal_power_contraction a b (m + 1) 0 B hstep
      (by rw [pow_zero, one_mul]; exact hfinal) (by omega)
    rw [hK, Nat.add_zero] at h
    exact h
  -- the last exact exponent is positive
  have ham : 1 ≤ a m := by
    by_contra h0
    have h0' : a m = 0 := by omega
    have h1 := hstep m (by omega)
    rw [h0', pow_zero, one_mul] at h1
    obtain ⟨u, hu⟩ := hodd m (by omega)
    cases m with
    | zero => omega
    | succ m' =>
        obtain ⟨v, hv⟩ := hodd m' (by omega)
        omega
  have hsplit : (∑ t ∈ Finset.range (m + 1), a t) =
      (∑ t ∈ Finset.range m, a t) + a m := Finset.sum_range_succ a m
  -- exact prefix up to step `m`
  have hpref := prefix_exact a b r K m hstart (fun i hi => hstep i (by omega))
    (fun i hi => hodd i (by omega)) (by
      intro i hi
      have hh : (∑ t ∈ Finset.range (i + 1), a t) ≤ ∑ t ∈ Finset.range m, a t :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (show i + 1 ≤ m by omega))
      omega) q m le_rfl
  obtain ⟨x, hx⟩ : ∃ x, x = b (m + 1) + 3 ^ (m + 1) * q := ⟨_, rfl⟩
  -- step `m + 1` lands on the odd part of `x`
  have hstepm : syracuseStep^[m + 1] (r + 2 ^ K * q) = x / 2 ^ x.factorization 2 := by
    rw [Function.iterate_succ_apply', hpref]
    unfold syracuseStep
    have hKm : K - ∑ t ∈ Finset.range m, a t = a m := by omega
    have hrow : 3 * (b m + 3 ^ m * 2 ^ (K - ∑ t ∈ Finset.range m, a t) * q) + 1 =
        2 ^ (a m) * x := by
      rw [hKm, hx]
      have hs := hstep m (by omega)
      calc
        3 * (b m + 3 ^ m * 2 ^ (a m) * q) + 1 =
            (3 * b m + 1) + 3 ^ (m + 1) * 2 ^ (a m) * q := by ring
        _ = _ := by rw [hs]; ring
    rw [hrow, Nat.ordCompl_self_pow_mul x (a m) Nat.prime_two]
  have hxpos : x ≠ 0 := by
    obtain ⟨u, hu⟩ := hodd m (by omega)
    omega
  obtain ⟨y, hy⟩ : ∃ y, y = x / 2 ^ x.factorization 2 := ⟨_, rfl⟩
  have hyodd : ¬ 2 ∣ y := by rw [hy]; exact Nat.not_dvd_ordCompl Nat.prime_two hxpos
  have hyle : y ≤ x := by rw [hy]; exact Nat.ordCompl_le x 2
  have hy2 : 3 * y + 1 = 2 ^ 1 * ((3 * y + 1) / 2) := by rw [pow_one]; omega
  have hlast := syracuseStep_le_of_pow_two_factor hy2
  have hmul : 3 ^ (m + 1 + 1) * q ≤ 2 ^ K * q := Nat.mul_le_mul_right q hc.le
  have h3x : 3 * x + 1 = B + 3 ^ (m + 1 + 1) * q := by
    rw [hx, ← hfinal]; ring
  rw [Function.iterate_succ_apply', hstepm, ← hy]
  omega

end CollatzFrontierAux

open CollatzFrontierAux

theorem solution
    (a b : ℕ → ℕ) (r K k e B : ℕ)
    (hstart : b 0 = r)
    (hstep : ∀ i < k, 3 * b i + 1 = 2 ^ (a i) * b (i + 1))
    (hodd : ∀ i < k, Odd (b (i + 1)))
    (hfinal : 3 * b k + 1 = 2 ^ e * B)
    (hbudget : (∑ i ∈ Finset.range k, a i) + e ≤ K)
    (hdesc : B < r) (q : ℕ) :
    syracuseStep^[k + 1] (r + 2 ^ K * q) < r + 2 ^ K * q := by
  have hc := terminal_power_contraction a b k e B hstep hfinal (by omega)
  by_cases hroom : 0 < e ∨ (∑ i ∈ Finset.range k, a i) < K
  · exact syracuse_terminal_budget a b r K k e B hstart hstep hodd hfinal hbudget
      hroom hc hdesc q
  · have he : e = 0 := by omega
    have hK : (∑ i ∈ Finset.range k, a i) = K := by omega
    subst he
    rw [pow_zero, one_mul] at hfinal
    cases k with
    | zero => omega
    | succ m => exact terminal_tight_case a b r K m B hstart hstep hodd hfinal hK hdesc q
