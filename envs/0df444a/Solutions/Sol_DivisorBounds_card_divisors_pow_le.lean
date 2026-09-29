-- Prove2me | solution 1 for DivisorBounds.card_divisors_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T17:26:23.480869+00:00
-- url     : https://prove2.me/submissions/3af500e6-2135-4548-87be-6a5fe860cc20

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.Chen.DivisorBound =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# DIV1 — the sub-polynomial divisor bound + the `hdiv` discharge

Design: `docs/blueprints/flags.md`, "2026-07-13 PE3c-4 ... CATCH #52 → DIV1"
and "THE PE3c-4 GATE".  This file supplies the missing analytic input flagged by
`Salt/Chen/AlphaClose.lean`'s named operating-point hypothesis

```
hdiv : (e.divisors.card : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5)
         ≤ Real.sqrt (X : ℝ)
```

(the exponent `A + 5` is `Real.rpow`, `A : ℝ`).  Catch #52 established that the
corpus bound `d(e) ≤ 2·√e` (`card_divisors_le_two_sqrt`) is INSUFFICIENT for this
cross-`M` term for `A > 1`; one needs `d(e)`'s true *sub-polynomial* size.

## The mathematics (elementary, explicit constants)

The classical `d(n) = O_ε(n^ε)` bound, made fully explicit.  Writing
`d(n) = ∏_{p^{k} ∥ n} (k+1)` and `n = ∏ p^{k}` over `n.primeFactors`, the per-prime
ratio `(k+1)/p^{kε}` is `≤ 1` once `p^ε ≥ 2` and is bounded by an explicit constant
otherwise.  Fixing `ε = 1/m` and splitting primes at the integer threshold `2^m`:

* **large primes** `p ≥ 2^m`:  `(k+1)^m ≤ (2^k)^m = (2^m)^k ≤ p^k`  (factor `1`);
* **small primes** `2 ≤ p < 2^m`:  `(k+1)^m ≤ (m/log 2)^m · 2^k ≤ (m/log 2)^m · p^k`,
  the constant coming from `k+1 ≤ (m/log 2)·2^{k/m}` (via `exp t ≥ 1 + t`).

There are at most `2^m` small primes, so
`d(n)^m ≤ (m/log 2)^{m·2^m} · n`, i.e. **`d(n) ≤ (m/log 2)^{2^m} · n^{1/m}`**
(`card_divisors_subpoly`, our explicit constant `C_m = (m/log 2)^{2^m}`).

## The discharge (`hdiv_discharge`)

At the balanced operating point `X ≍ M ≍ √x`, `e ≤ D ≍ √x/L^{A+5}` (supplied by the
H-glue as the hypotheses `D ≤ √x`, `√x ≤ 4·X`, `X·M ≤ x²`), taking `m = 3`
(`ε = 1/3 < 1/2`) gives `d(e) ≤ C₃·(√x)^{1/3} = C₃·x^{1/6}`, `L ≤ 2 log x`, so

```
d(e)·L^{A+5} ≤ C₃·x^{1/6}·(2 log x)^{A+5} ≤ ½·x^{1/4} ≤ √X
```

for `x ≥ x₀`, the middle step because `(2 log x)^{A+5} = o(x^{1/12})`
(`isLittleO_log_rpow_rpow_atTop`).  `hdiv_discharge` states exactly the `hdiv`
inequality of `AlphaClose`, parametric in `A`, under those operating relations.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`,
no new axioms.  One documented cost: none beyond the default heartbeat budget.
-/

namespace Salt.Chen

open Finset

/-! ## The per-small-prime constant `(k+1)^m ≤ (m/log 2)^m · 2^k`. -/

/-- The clean real bound underlying the small-prime factor:
`(k+1)^m ≤ (m/log 2)^m · 2^k`.  Route: `2^{k/m} = exp((k/m)·log 2) ≥ 1 + (k/m)·log 2`,
so `(m/log 2)·2^{k/m} ≥ m/log 2 + k ≥ k+1` (as `log 2 ≤ 1 ≤ m`); raise to the `m`. -/
private lemma succ_pow_le_const (m k : ℕ) (hm : 1 ≤ m) :
    ((k : ℝ) + 1) ^ m ≤ ((m : ℝ) / Real.log 2) ^ m * (2 : ℝ) ^ k := by
  have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have hML : (0 : ℝ) < (m : ℝ) / Real.log 2 := div_pos hmR hL2
  -- `log 2 ≤ 1`, hence `1 ≤ m/log 2`.
  have h1leML : (1 : ℝ) ≤ (m : ℝ) / Real.log 2 := by
    rw [le_div_iff₀ hL2]
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  -- `2^{k/m} ≥ 1 + (k/m)·log 2`.
  have hexp : (1 : ℝ) + ((k : ℝ) / m) * Real.log 2 ≤ (2 : ℝ) ^ ((k : ℝ) / m) := by
    rw [Real.rpow_def_of_pos (show (0 : ℝ) < 2 by norm_num)]
    calc (1 : ℝ) + ((k : ℝ) / m) * Real.log 2
        = ((k : ℝ) / m) * Real.log 2 + 1 := by ring
      _ ≤ Real.exp (((k : ℝ) / m) * Real.log 2) := Real.add_one_le_exp _
      _ = Real.exp (Real.log 2 * ((k : ℝ) / m)) := by rw [mul_comm]
  -- base inequality `k+1 ≤ (m/log 2)·2^{k/m}`.
  have hbase : (k : ℝ) + 1 ≤ ((m : ℝ) / Real.log 2) * (2 : ℝ) ^ ((k : ℝ) / m) := by
    have h2 : ((m : ℝ) / Real.log 2) * (1 + ((k : ℝ) / m) * Real.log 2)
        ≤ ((m : ℝ) / Real.log 2) * (2 : ℝ) ^ ((k : ℝ) / m) :=
      mul_le_mul_of_nonneg_left hexp hML.le
    have heq : ((m : ℝ) / Real.log 2) * (1 + ((k : ℝ) / m) * Real.log 2)
        = (m : ℝ) / Real.log 2 + (k : ℝ) := by field_simp
    rw [heq] at h2; linarith
  -- raise to the power `m`, and `(2^{k/m})^m = 2^k`.
  have hpow : ((2 : ℝ) ^ ((k : ℝ) / m)) ^ m = (2 : ℝ) ^ k := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((k : ℝ) / m)) m,
        ← Real.rpow_mul (show (0 : ℝ) ≤ 2 by norm_num), div_mul_cancel₀ (k : ℝ) hmne,
        Real.rpow_natCast]
  calc ((k : ℝ) + 1) ^ m
      ≤ (((m : ℝ) / Real.log 2) * (2 : ℝ) ^ ((k : ℝ) / m)) ^ m :=
        pow_le_pow_left₀ (by positivity) hbase m
    _ = ((m : ℝ) / Real.log 2) ^ m * ((2 : ℝ) ^ ((k : ℝ) / m)) ^ m := by rw [mul_pow]
    _ = ((m : ℝ) / Real.log 2) ^ m * (2 : ℝ) ^ k := by rw [hpow]

/-! ## The multiplicative bound `d(n)^m ≤ (m/log 2)^{m·2^m}·n`. -/

/-- The elementary multiplicative sub-polynomial bound, over `ℝ`:
`d(n)^m ≤ (m/log 2)^{m·2^m}·n` for `1 ≤ n`, `1 ≤ m`.  Proof by the per-prime split
described in the header. -/
theorem card_divisors_pow_le (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (hn : 1 ≤ n) :
    ((n.divisors.card : ℝ)) ^ m ≤ ((m : ℝ) / Real.log 2) ^ (m * 2 ^ m) * (n : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set S : Finset ℕ := n.primeFactors with hS
  -- `d(n) = ∏_{p∈S} (fp+1)` and `n = ∏_{p∈S} p^{fp}`.
  have hd : (n.divisors.card : ℝ) = ∏ p ∈ S, ((n.factorization p + 1 : ℕ) : ℝ) := by
    rw [Nat.card_divisors hn0, ← hS, Nat.cast_prod]
  have hnnat : (n : ℝ) = ∏ p ∈ S, (p : ℝ) ^ (n.factorization p) := by
    have hnat : n = ∏ p ∈ S, p ^ (n.factorization p) := by
      rw [hS]
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
      simp only [Finsupp.prod, Nat.support_factorization]
    conv_lhs => rw [hnat]
    rw [Nat.cast_prod]; simp only [Nat.cast_pow]
  -- the per-prime bound.
  have hterm : ∀ p ∈ S, ((n.factorization p + 1 : ℕ) : ℝ) ^ m
      ≤ (if p < 2 ^ m then ((m : ℝ) / Real.log 2) ^ m else 1)
          * (p : ℝ) ^ (n.factorization p) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors (hS ▸ hp)).two_le
    set fp := n.factorization p with hfp
    by_cases hpc : p < 2 ^ m
    · rw [if_pos hpc]
      have h1 := succ_pow_le_const m fp hm
      have h2 : (2 : ℝ) ^ fp ≤ (p : ℝ) ^ fp :=
        pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hp2) fp
      calc ((fp + 1 : ℕ) : ℝ) ^ m = ((fp : ℝ) + 1) ^ m := by push_cast; ring
        _ ≤ ((m : ℝ) / Real.log 2) ^ m * (2 : ℝ) ^ fp := h1
        _ ≤ ((m : ℝ) / Real.log 2) ^ m * (p : ℝ) ^ fp :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
    · rw [if_neg hpc]
      have hge : 2 ^ m ≤ p := Nat.not_lt.mp hpc
      have hnat : (fp + 1) ^ m ≤ p ^ fp := by
        calc (fp + 1) ^ m ≤ (2 ^ fp) ^ m := Nat.pow_le_pow_left fp.lt_two_pow_self m
          _ = (2 ^ m) ^ fp := by rw [← pow_mul, Nat.mul_comm fp m, pow_mul]
          _ ≤ p ^ fp := Nat.pow_le_pow_left hge fp
      calc ((fp + 1 : ℕ) : ℝ) ^ m = (((fp + 1) ^ m : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((p ^ fp : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = 1 * (p : ℝ) ^ fp := by push_cast; ring
  -- the small-prime count and the product bound `∏ Bp ≤ (m/log 2)^{m·2^m}`.
  have hBcount : (S.filter (fun p => p < 2 ^ m)).card ≤ 2 ^ m := by
    have hsub : S.filter (fun p => p < 2 ^ m) ⊆ Finset.range (2 ^ m) := by
      intro p hp; rw [Finset.mem_filter] at hp; rw [Finset.mem_range]; exact hp.2
    calc (S.filter (fun p => p < 2 ^ m)).card
        ≤ (Finset.range (2 ^ m)).card := Finset.card_le_card hsub
      _ = 2 ^ m := Finset.card_range _
  have h1leML : (1 : ℝ) ≤ (m : ℝ) / Real.log 2 := by
    rw [le_div_iff₀ hL2]
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have h1leB : (1 : ℝ) ≤ ((m : ℝ) / Real.log 2) ^ m := one_le_pow₀ h1leML
  have hBprod : ∏ p ∈ S, (if p < 2 ^ m then ((m : ℝ) / Real.log 2) ^ m else (1 : ℝ))
      ≤ ((m : ℝ) / Real.log 2) ^ (m * 2 ^ m) := by
    rw [(Finset.prod_filter (fun p => p < 2 ^ m) (fun _ => ((m : ℝ) / Real.log 2) ^ m)).symm,
        Finset.prod_const, ← pow_mul]
    exact pow_le_pow_right₀ h1leML (Nat.mul_le_mul le_rfl hBcount)
  -- assemble.
  calc ((n.divisors.card : ℝ)) ^ m
      = (∏ p ∈ S, ((n.factorization p + 1 : ℕ) : ℝ)) ^ m := by rw [hd]
    _ = ∏ p ∈ S, ((n.factorization p + 1 : ℕ) : ℝ) ^ m := (Finset.prod_pow S m _).symm
    _ ≤ ∏ p ∈ S, (if p < 2 ^ m then ((m : ℝ) / Real.log 2) ^ m else 1)
          * (p : ℝ) ^ (n.factorization p) :=
        Finset.prod_le_prod (fun p _ => by positivity) hterm
    _ = (∏ p ∈ S, (if p < 2 ^ m then ((m : ℝ) / Real.log 2) ^ m else 1))
          * (∏ p ∈ S, (p : ℝ) ^ (n.factorization p)) := Finset.prod_mul_distrib
    _ = (∏ p ∈ S, (if p < 2 ^ m then ((m : ℝ) / Real.log 2) ^ m else 1)) * (n : ℝ) := by
        rw [← hnnat]
    _ ≤ ((m : ℝ) / Real.log 2) ^ (m * 2 ^ m) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hBprod (by positivity)

/-! ## The sub-polynomial bound `d(n) ≤ (m/log 2)^{2^m}·n^{1/m}`. -/

/-- **The explicit sub-polynomial divisor bound.**  `d(n) ≤ C_m · n^{1/m}` with the
explicit constant `C_m = (m/log 2)^{2^m}`, for `1 ≤ n`, `1 ≤ m`.  Obtained from
`card_divisors_pow_le` by taking the `1/m`-power. -/
theorem card_divisors_subpoly (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (hn : 1 ≤ n) :
    (n.divisors.card : ℝ)
      ≤ ((m : ℝ) / Real.log 2) ^ (2 ^ m) * (n : ℝ) ^ ((1 : ℝ) / m) := by
  have hmne : (m : ℝ) ≠ 0 := by positivity
  have hmne' : (m : ℕ) ≠ 0 := by omega
  have hpow := card_divisors_pow_le m hm n hn
  have hdnn : (0 : ℝ) ≤ (n.divisors.card : ℝ) := by positivity
  -- `d = (d^m)^{1/m}`.
  have hcast : (n.divisors.card : ℝ) = ((n.divisors.card : ℝ) ^ m) ^ ((1 : ℝ) / m) := by
    rw [← Real.rpow_natCast (n.divisors.card : ℝ) m, ← Real.rpow_mul hdnn,
        mul_one_div, div_self (by exact_mod_cast hmne'), Real.rpow_one]
  rw [hcast]
  have hone_div : (0 : ℝ) ≤ (1 : ℝ) / m := by positivity
  calc ((n.divisors.card : ℝ) ^ m) ^ ((1 : ℝ) / m)
      ≤ (((m : ℝ) / Real.log 2) ^ (m * 2 ^ m) * (n : ℝ)) ^ ((1 : ℝ) / m) :=
        Real.rpow_le_rpow (pow_nonneg hdnn m) hpow hone_div
    _ = (((m : ℝ) / Real.log 2) ^ (m * 2 ^ m)) ^ ((1 : ℝ) / m)
          * (n : ℝ) ^ ((1 : ℝ) / m) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
    _ = ((m : ℝ) / Real.log 2) ^ (2 ^ m) * (n : ℝ) ^ ((1 : ℝ) / m) := by
        congr 1
        rw [← Real.rpow_natCast ((m : ℝ) / Real.log 2) (m * 2 ^ m),
            ← Real.rpow_mul (by positivity),
            ← Real.rpow_natCast ((m : ℝ) / Real.log 2) (2 ^ m)]
        congr 1
        push_cast
        field_simp

/-- The `m = 3` specialization, with the constant normalized to `(3/log 2)^8`,
in the exact shape the discharge consumes. -/
theorem card_divisors_cube_root (n : ℕ) (hn : 1 ≤ n) :
    (n.divisors.card : ℝ) ≤ ((3 : ℝ) / Real.log 2) ^ 8 * (n : ℝ) ^ ((1 : ℝ) / 3) := by
  have h := card_divisors_subpoly 3 (by norm_num) n hn
  exact_mod_cast h

/-! ## The `hdiv` discharge at the operating point. -/

/-- **`hdiv_discharge` — the operating-point discharge of `AlphaClose`'s `hdiv`.**

There is a threshold `x₀` such that, for `x ≥ x₀` and any `X M D : ℕ` satisfying the
balanced operating relations
* `hDx  : (D : ℝ) ≤ √x`          (`D ≍ √x/L^{A+5}`),
* `hXx  : √x ≤ 4·X`              (`X ≍ √x`),
* `hXM  : X·M ≤ x²`              (`X·M ≍ x`),
and any `e` with `1 ≤ e ≤ D`, the exact `hdiv` inequality of `AlphaClose` holds:

```
(e.divisors.card : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5) ≤ Real.sqrt (X : ℝ).
```

The H-glue supplies the three operating relations at its operating point. -/
theorem hdiv_discharge {A : ℝ} (hA : 0 ≤ A) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (X M D : ℕ),
      1 ≤ X → 1 ≤ M →
      (D : ℝ) ≤ Real.sqrt x →
      Real.sqrt x ≤ 4 * (X : ℝ) →
      (X : ℝ) * (M : ℝ) ≤ x ^ 2 →
      ∀ e : ℕ, 1 ≤ e → e ≤ D →
        (e.divisors.card : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5)
          ≤ Real.sqrt (X : ℝ) := by
  set C : ℝ := ((3 : ℝ) / Real.log 2) ^ 8 with hC
  have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCpos : 0 < C := by rw [hC]; exact pow_pos (div_pos (by norm_num) hL2) 8
  set K : ℝ := 2 * C * (2 : ℝ) ^ (A + 5) with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  -- the analytic heart: `2·C·(2 log x)^{A+5} ≤ x^{1/12}` eventually.
  have hlo : (fun x : ℝ => Real.log x ^ (A + 5))
      =o[Filter.atTop] (fun x => x ^ ((1 : ℝ) / 12)) :=
    isLittleO_log_rpow_rpow_atTop (A + 5) (by norm_num)
  have hev1 : ∀ᶠ x : ℝ in Filter.atTop,
      ‖Real.log x ^ (A + 5)‖ ≤ (1 / K) * ‖x ^ ((1 : ℝ) / 12)‖ := hlo.def (by positivity)
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      2 * C * (2 * Real.log x) ^ (A + 5) ≤ x ^ ((1 : ℝ) / 12) := by
    filter_upwards [hev1, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hlogpos : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
    have hxpos : (0 : ℝ) < x := by linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlogpos _),
        Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le _)] at hx
    have hmul : (2 * Real.log x) ^ (A + 5) = (2 : ℝ) ^ (A + 5) * Real.log x ^ (A + 5) :=
      Real.mul_rpow (by norm_num) hlogpos
    calc 2 * C * (2 * Real.log x) ^ (A + 5)
        = K * Real.log x ^ (A + 5) := by rw [hmul, hK]; ring
      _ ≤ K * ((1 / K) * x ^ ((1 : ℝ) / 12)) := mul_le_mul_of_nonneg_left hx hKpos.le
      _ = x ^ ((1 : ℝ) / 12) := by field_simp
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max x₁ 1, ?_⟩
  intro x hx X M D h1X h1M hDx hXx hXM e h1e heD
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hxx1 : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hxpos : (0 : ℝ) < x := by linarith
  have heart := hx₁ x hxx1
  -- Step A: `d(e) ≤ C·x^{1/6}`.
  have hsub : (e.divisors.card : ℝ) ≤ C * (e : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [hC]; exact card_divisors_cube_root e h1e
  have hle_sx : (e : ℝ) ≤ Real.sqrt x := le_trans (by exact_mod_cast heD) hDx
  have hsx13 : (Real.sqrt x) ^ ((1 : ℝ) / 3) = x ^ ((1 : ℝ) / 6) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hxpos.le]; congr 1; norm_num
  have he13 : (e : ℝ) ^ ((1 : ℝ) / 3) ≤ x ^ ((1 : ℝ) / 6) := by
    rw [← hsx13]; exact Real.rpow_le_rpow (by positivity) hle_sx (by norm_num)
  have hsub2 : (e.divisors.card : ℝ) ≤ C * x ^ ((1 : ℝ) / 6) :=
    le_trans hsub (mul_le_mul_of_nonneg_left he13 hCpos.le)
  -- Step B: `L = log(XM)`, `0 ≤ L ≤ 2 log x`.
  have hXM1 : (1 : ℝ) ≤ (X : ℝ) * (M : ℝ) := by
    have : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast h1X
    have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast h1M
    nlinarith [this, (by exact_mod_cast h1X : (1 : ℝ) ≤ (X : ℝ))]
  have hLnn : (0 : ℝ) ≤ Real.log ((X : ℝ) * (M : ℝ)) := Real.log_nonneg hXM1
  have hL2logx : Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * Real.log x := by
    have hx2pos : (0 : ℝ) < x ^ 2 := by positivity
    have : Real.log ((X : ℝ) * (M : ℝ)) ≤ Real.log (x ^ 2) :=
      (Real.log_le_log_iff (by linarith) hx2pos).mpr hXM
    rwa [Real.log_pow] at this
    -- log (x^2) = 2 * log x
  have hLpow : Real.log ((X : ℝ) * (M : ℝ)) ^ (A + 5) ≤ (2 * Real.log x) ^ (A + 5) :=
    Real.rpow_le_rpow hLnn hL2logx (by linarith)
  -- Step C: `C·x^{1/6}·(2 log x)^{A+5} ≤ ½·x^{1/4}`.
  have hstar : C * x ^ ((1 : ℝ) / 6) * (2 * Real.log x) ^ (A + 5)
      ≤ (1 / 2) * x ^ ((1 : ℝ) / 4) := by
    have hre : C * x ^ ((1 : ℝ) / 6) * (2 * Real.log x) ^ (A + 5)
        = (1 / 2) * x ^ ((1 : ℝ) / 6) * (2 * C * (2 * Real.log x) ^ (A + 5)) := by ring
    rw [hre]
    have hsum : (1 : ℝ) / 6 + 1 / 12 = 1 / 4 := by norm_num
    calc (1 / 2) * x ^ ((1 : ℝ) / 6) * (2 * C * (2 * Real.log x) ^ (A + 5))
        ≤ (1 / 2) * x ^ ((1 : ℝ) / 6) * x ^ ((1 : ℝ) / 12) :=
          mul_le_mul_of_nonneg_left heart (by positivity)
      _ = (1 / 2) * x ^ ((1 : ℝ) / 4) := by
          rw [mul_assoc, ← Real.rpow_add hxpos, hsum]
  -- Step D: `½·x^{1/4} ≤ √X`.
  have hfin : (1 / 2 : ℝ) * x ^ ((1 : ℝ) / 4) ≤ Real.sqrt (X : ℝ) := by
    have he2 : ((1 / 2 : ℝ) * x ^ ((1 : ℝ) / 4)) ^ 2 = 1 / 4 * x ^ ((1 : ℝ) / 2) := by
      have hin : (x ^ ((1 : ℝ) / 4)) ^ 2 = x ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_natCast (x ^ ((1 : ℝ) / 4)) 2, ← Real.rpow_mul hxpos.le]
        congr 1; norm_num
      rw [mul_pow, hin]; norm_num
    rw [Real.le_sqrt (by positivity) (by positivity), he2, ← Real.sqrt_eq_rpow]
    linarith [hXx]
  -- assemble the chain.
  calc (e.divisors.card : ℝ) * Real.log ((X : ℝ) * (M : ℝ)) ^ (A + 5)
      ≤ (C * x ^ ((1 : ℝ) / 6)) * (2 * Real.log x) ^ (A + 5) :=
        mul_le_mul hsub2 hLpow (Real.rpow_nonneg hLnn _) (by positivity)
    _ ≤ (1 / 2) * x ^ ((1 : ℝ) / 4) := hstar
    _ ≤ Real.sqrt (X : ℝ) := hfin

end Salt.Chen

end




section
open Finset

theorem solution (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (hn : 1 ≤ n) :
    ((n.divisors.card : ℝ)) ^ m ≤ ((m : ℝ) / Real.log 2) ^ (m * 2 ^ m) * (n : ℝ) := by
  apply Salt.Chen.card_divisors_pow_le <;> assumption

end

