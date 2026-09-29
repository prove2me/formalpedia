-- Prove2me | solution 1 for DirichletLFunctions.LSeries_toArithmeticFunction_eq
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T17:58:14.530857+00:00
-- url     : https://prove2.me/submissions/c9d360d4-4586-473d-bf0a-e684c4c85f2d

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.SW.FourFold =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# The SW rung, node S4a — the 4-fold nonnegativity

Design: `docs/blueprints/sw.md`, wave S4 (the "⚠️ NEW SUB-NODE": the two-distinct-real-characters
positivity input for Siegel via Goldfeld). Goldfeld's proof of Siegel's theorem runs the positivity
engine on the completed product
`F(s) = ζ(s)·L(s,χ₁)·L(s,χ₂)·L(s,χ₁χ₂)` for two real (quadratic) characters. Mathlib's
`DirichletCharacter.zetaMul` covers only the **2-fold** case `ζ·L(χ)`; this module supplies the
**4-fold** analogue.

## What mathlib provides vs. what we build

* Engine (character-agnostic, ready): `LSeries.positive`,
  `LSeries.positive_of_differentiable_of_eqOn`, `LSeries.iteratedDeriv_alternating`
  (`Mathlib/NumberTheory/LSeries/Positivity.lean`). These consume an arithmetic function with
  nonnegative coefficients and value `1` at `n = 1`.
* 2-fold template: `DirichletCharacter.zetaMul χ = ζ ⍟ χ`, `zetaMul_nonneg` (for `χ² = 1`),
  `isMultiplicative_zetaMul`, `LSeriesSummable_zetaMul`, `BadChar.F_eq_LSeries`
  (`Mathlib/NumberTheory/LSeries/Nonvanishing.lean`). We reuse `zetaMul` as a building block.

## The character packaging (`changeLevel`)

The natural home for the four characters is a common level. Given `χ₁ : DirichletCharacter ℂ q₁`
and `χ₂ : DirichletCharacter ℂ q₂`, lift both to `N = q₁ * q₂` via `changeLevel`:
`χ₁' := changeLevel (dvd_mul_right q₁ q₂) χ₁`, `χ₂' := changeLevel (dvd_mul_left q₂ q₁) χ₂`, and the
character product is the monoid product `χ₁' * χ₂'` at level `N`. `changeLevel` is a `MonoidHom`, so
`(changeLevel h χ)² = changeLevel h (χ²) = 1` whenever `χ² = 1` (`changeLevel_quadratic`). The core
results are stated for **any** two same-level quadratic characters (imprimitive allowed — everything
here lives on `Re s > 1`, no analytic continuation needed for the L-series identity), and the
`changeLevel` maps merely produce such a pair.

## Deliverables

1. `fourfold_vonMangoldt_nonneg` — the Λ-level (log-derivative) positivity via the factorisation
   `1 + χ₁ + χ₂ + χ₁χ₂ = (1 + χ₁)(1 + χ₂)` at real values in `{-1,0,1}`.
2. `fourfoldCoeff` (the Dirichlet coefficients of `F`, `= ζ ⍟ χ₁ ⍟ χ₂ ⍟ χ₁χ₂`), its
   multiplicativity, value `1` at `n = 1`, summability, and the L-series product identity
   `LSeries (fourfoldCoeff χ₁ χ₂) s = riemannZeta s * L χ₁ s * L χ₂ s * L (χ₁χ₂) s` on `Re s > 1`.
-/

namespace Salt.SW

open Complex DirichletCharacter ArithmeticFunction
open scoped LSeries.notation ComplexOrder ArithmeticFunction ArithmeticFunction.zeta

variable {N : ℕ}

/-! ## 1. Quadratic characters take values in `{0, 1, -1}` -/

/-- A quadratic character (`χ² = 1`) takes only the values `0`, `1`, `-1`. This is
`MulChar.isQuadratic_iff_sq_eq_one` specialised to a natural-number argument. -/
lemma quadratic_apply_mem {χ : DirichletCharacter ℂ N} (hχ : χ ^ 2 = 1) (n : ℕ) :
    χ n = 0 ∨ χ n = 1 ∨ χ n = -1 :=
  MulChar.isQuadratic_iff_sq_eq_one.mpr hχ (n : ZMod N)

/-! ## 2. Deliverable 1 — the Λ-level (log-derivative) positivity -/

/-- **The 4-fold von Mangoldt positivity.** For real characters `χ₁, χ₂` (`χᵢ² = 1`) the weight
`1 + χ₁(n) + χ₂(n) + (χ₁χ₂)(n)` is `(1 + χ₁(n))(1 + χ₂(n)) ≥ 0` at the real values `{-1,0,1}`, so
`Λ(n)·(1 + Re χ₁(n) + Re χ₂(n) + Re (χ₁χ₂)(n)) ≥ 0`. This is the coefficient-level input to the
positivity of `−(ζ'/ζ + L'/L(χ₁) + L'/L(χ₂) + L'/L(χ₁χ₂))` that Goldfeld's argument consumes. -/
theorem fourfold_vonMangoldt_nonneg {χ₁ χ₂ : DirichletCharacter ℂ N}
    (hχ₁ : χ₁ ^ 2 = 1) (hχ₂ : χ₂ ^ 2 = 1) (n : ℕ) :
    0 ≤ Λ n * (1 + (χ₁ n).re + (χ₂ n).re + ((χ₁ * χ₂) n).re) := by
  refine mul_nonneg vonMangoldt_nonneg ?_
  rw [MulChar.mul_apply]
  rcases quadratic_apply_mem hχ₁ n with h1 | h1 | h1 <;>
    rcases quadratic_apply_mem hχ₂ n with h2 | h2 | h2 <;>
    rw [h1, h2] <;> norm_num

/-! ## 3. The 4-fold coefficient function and the L-series product identity -/

/-- The Dirichlet coefficients of `F(s) = ζ(s)·L(s,χ₁)·L(s,χ₂)·L(s,χ₁χ₂)`, packaged as the
convolution `ζ ⍟ χ₁ ⍟ χ₂ ⍟ (χ₁χ₂)` (built on mathlib's `zetaMul χ₁ = ζ ⍟ χ₁`). -/
noncomputable def fourfoldCoeff (χ₁ χ₂ : DirichletCharacter ℂ N) : ArithmeticFunction ℂ :=
  zetaMul χ₁ * toArithmeticFunction (χ₂ ·) * toArithmeticFunction ((χ₁ * χ₂) ·)

/-- `fourfoldCoeff` is multiplicative. -/
lemma isMultiplicative_fourfoldCoeff (χ₁ χ₂ : DirichletCharacter ℂ N) :
    (fourfoldCoeff χ₁ χ₂).IsMultiplicative :=
  ((isMultiplicative_zetaMul χ₁).mul (isMultiplicative_toArithmeticFunction χ₂)).mul
    (isMultiplicative_toArithmeticFunction (χ₁ * χ₂))

/-- `fourfoldCoeff χ₁ χ₂ 1 = 1`. -/
@[simp]
lemma fourfoldCoeff_apply_one (χ₁ χ₂ : DirichletCharacter ℂ N) :
    fourfoldCoeff χ₁ χ₂ 1 = 1 :=
  (isMultiplicative_fourfoldCoeff χ₁ χ₂).map_one

/-! ## 4. Deliverable 2 — nonnegativity of the coefficients

`fourfoldCoeff` is multiplicative, so nonnegativity reduces to prime powers. At a prime power we
use the pairing `fourfoldCoeff = zetaMul χ₁ ⍟ (χ₂ ⍟ χ₁χ₂)` where `zetaMul χ₁ ≥ 0` (mathlib's
`zetaMul_nonneg`) and the paired factor evaluates to `(χ₂ p)ʲ · zetaMul χ₁ (pʲ)` (`h_prime_pow`).
The nonnegativity of `∑ᵢ zetaMul χ₁(pⁱ)·(χ₂ p)ᵏ⁻ⁱ·zetaMul χ₁(pᵏ⁻ⁱ)` then splits on the value
`χ₂ p ∈ {0,1,-1}`: for `0,1` every term is nonnegative; for `-1` we reduce to the alternating
convolution `altconv_nonneg`, itself handled by parity (`0` and `-1` per-term, `1` by the
telescoping `Tval`). -/

/-- Prime-power evaluation of a convolution of arithmetic functions. -/
lemma mul_apply_prime_pow {f g : ArithmeticFunction ℂ} {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (f * g) (p ^ k) = ∑ i ∈ Finset.range (k + 1), f (p ^ i) * g (p ^ (k - i)) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun d e => f d * g e),
    Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hp.pos]

/-- Prime-power values of `zetaMul χ` as a geometric sum. -/
lemma zetaMul_prime_pow_eq (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    zetaMul χ (p ^ k) = ∑ i ∈ Finset.range (k + 1), (χ p) ^ i := by
  rw [zetaMul, coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← χ.apply_eq_toArithmeticFunction_apply (pow_ne_zero i hp.ne_zero), Nat.cast_pow, map_pow]

/-- Prime-power values of the Dirichlet coefficients of a character. -/
lemma toArithmeticFunction_prime_pow (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (toArithmeticFunction (χ ·)) (p ^ a) = (χ p) ^ a := by
  rw [← χ.apply_eq_toArithmeticFunction_apply (pow_ne_zero a hp.ne_zero), Nat.cast_pow, map_pow]

/-- The paired factor `χ₂ ⍟ (χ₁χ₂)` at a prime power equals `(χ₂ p)ʲ · zetaMul χ₁ (pʲ)`. -/
lemma h_prime_pow (χ₁ χ₂ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    (toArithmeticFunction (χ₂ ·) * toArithmeticFunction ((χ₁ * χ₂) ·)) (p ^ j)
      = (χ₂ p) ^ j * zetaMul χ₁ (p ^ j) := by
  rw [mul_apply_prime_pow hp]
  have step : ∀ a ∈ Finset.range (j + 1),
      (toArithmeticFunction (χ₂ ·)) (p ^ a) * (toArithmeticFunction ((χ₁ * χ₂) ·)) (p ^ (j - a))
        = (χ₂ p) ^ j * (χ₁ p) ^ (j - a) := by
    intro a ha
    have hle : a + (j - a) = j := Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))
    rw [toArithmeticFunction_prime_pow χ₂ hp, toArithmeticFunction_prime_pow (χ₁ * χ₂) hp,
      MulChar.mul_apply, mul_pow,
      show (χ₂ (p : ZMod N)) ^ a * ((χ₁ (p : ZMod N)) ^ (j - a) * (χ₂ (p : ZMod N)) ^ (j - a))
          = (χ₂ (p : ZMod N)) ^ (a + (j - a)) * (χ₁ (p : ZMod N)) ^ (j - a) by ring, hle]
  rw [Finset.sum_congr rfl step, ← Finset.mul_sum, zetaMul_prime_pow_eq χ₁ hp]
  congr 1
  exact Finset.sum_range_reflect (fun a => (χ₁ (p : ZMod N)) ^ a) (j + 1)

/-- The reduction of `fourfoldCoeff` at a prime power to the paired convolution sum. -/
lemma fourfoldCoeff_prime_pow (χ₁ χ₂ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    fourfoldCoeff χ₁ χ₂ (p ^ k)
      = ∑ i ∈ Finset.range (k + 1),
          zetaMul χ₁ (p ^ i) * (χ₂ p) ^ (k - i) * zetaMul χ₁ (p ^ (k - i)) := by
  rw [fourfoldCoeff, mul_assoc, mul_apply_prime_pow hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h_prime_pow χ₁ χ₂ hp, ← mul_assoc]

private lemma neg_one_two_mul (n : ℕ) : (-1 : ℂ) ^ (2 * n) = 1 :=
  Even.neg_one_pow ⟨n, by ring⟩

/-- `Rval k = ∑_{i≤k} (-1)ⁱ (i+1)`. -/
private noncomputable def Rval (k : ℕ) : ℂ := ∑ i ∈ Finset.range (k + 1), (-1) ^ i * ((i : ℂ) + 1)

/-- `Tval k = ∑_{i≤k} (-1)ⁱ (i+1)(k+1-i)`. -/
private noncomputable def Tval (k : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (k + 1), (-1) ^ i * ((i : ℂ) + 1) * ((k : ℂ) + 1 - (i : ℂ))

private lemma Rval_succ (k : ℕ) : Rval (k + 1) = Rval k + (-1) ^ (k + 1) * ((k : ℂ) + 2) := by
  simp only [Rval]; rw [Finset.sum_range_succ]; push_cast; ring

private lemma Tval_succ (k : ℕ) : Tval (k + 1) = Tval k + Rval (k + 1) := by
  have pt : ∀ i : ℕ, (-1 : ℂ) ^ i * ((i : ℂ) + 1) * (((k + 1 : ℕ) : ℂ) + 1 - (i : ℂ))
      = (-1) ^ i * ((i : ℂ) + 1) * ((k : ℂ) + 1 - (i : ℂ)) + (-1) ^ i * ((i : ℂ) + 1) := by
    intro i; push_cast; ring
  rw [Rval_succ, Tval, Finset.sum_range_succ (n := k + 1),
    Finset.sum_congr rfl (fun i (_ : i ∈ Finset.range (k + 1)) => pt i),
    Finset.sum_add_distrib]
  simp only [Tval, Rval]
  push_cast; ring

/-- Closed form of `Rval` at even and odd arguments. -/
private lemma Rval_closed (t : ℕ) :
    Rval (2 * t) = (t : ℂ) + 1 ∧ Rval (2 * t + 1) = -((t : ℂ) + 1) := by
  induction t with
  | zero =>
    refine ⟨?_, ?_⟩ <;> simp only [Rval, Nat.mul_zero, Nat.zero_add] <;>
      rw [Finset.sum_range_succ] <;> simp
  | succ t ih =>
    obtain ⟨_, ih2⟩ := ih
    have heven : Rval (2 * (t + 1)) = ((t : ℂ) + 1) + 1 := by
      rw [show 2 * (t + 1) = (2 * t + 1) + 1 by ring, Rval_succ, ih2,
        show 2 * t + 1 + 1 = 2 * (t + 1) by ring, neg_one_two_mul]
      push_cast; ring
    refine ⟨by rw [heven]; push_cast; ring, ?_⟩
    rw [Rval_succ, heven]
    have : (-1 : ℂ) ^ (2 * (t + 1) + 1) = -1 := by rw [pow_succ, neg_one_two_mul]; ring
    rw [this]; push_cast; ring

/-- Closed form of `Tval`: nonnegative at even arguments, `0` at odd. -/
private lemma Tval_closed (t : ℕ) : Tval (2 * t) = (t : ℂ) + 1 ∧ Tval (2 * t + 1) = 0 := by
  induction t with
  | zero =>
    refine ⟨?_, ?_⟩ <;> simp only [Tval, Nat.mul_zero, Nat.zero_add] <;>
      rw [Finset.sum_range_succ] <;> simp
  | succ t ih =>
    obtain ⟨_, ih2⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [show 2 * (t + 1) = (2 * t + 1) + 1 by ring, Tval_succ, ih2, zero_add,
        show 2 * t + 1 + 1 = 2 * (t + 1) by ring, (Rval_closed (t + 1)).1]
    · rw [show 2 * (t + 1) + 1 = (2 * (t + 1)) + 1 by ring, Tval_succ,
        show 2 * (t + 1) = (2 * t + 1) + 1 by ring, Tval_succ, ih2, zero_add,
        show 2 * t + 1 + 1 = 2 * (t + 1) by ring, (Rval_closed (t + 1)).1, Rval_succ,
        (Rval_closed (t + 1)).1]
      have : (-1 : ℂ) ^ (2 * (t + 1) + 1) = -1 := by rw [pow_succ, neg_one_two_mul]; ring
      rw [this]; push_cast; ring

/-- The `c = 1` alternating convolution is nonnegative (via the telescoping `Tval`). -/
private lemma altconv_one (k : ℕ) :
    0 ≤ ∑ i ∈ Finset.range (k + 1),
      ((i : ℂ) + 1) * (-1) ^ (k - i) * ((↑(k - i) : ℂ) + 1) := by
  have hbridge : (∑ i ∈ Finset.range (k + 1),
      ((i : ℂ) + 1) * (-1) ^ (k - i) * ((↑(k - i) : ℂ) + 1)) = Tval k := by
    rw [Tval, ← Finset.sum_range_reflect
      (fun i => (-1 : ℂ) ^ i * ((i : ℂ) + 1) * ((k : ℂ) + 1 - (i : ℂ))) (k + 1)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : k + 1 - 1 - i = k - i := by omega
    have h2 : (↑(k - i) : ℂ) = (k : ℂ) - (i : ℂ) := by rw [Nat.cast_sub hik]
    rw [h1, h2]; ring
  rw [hbridge]
  rcases Nat.even_or_odd k with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [ht, show t + t = 2 * t by ring, (Tval_closed t).1]
    exact add_nonneg (by exact_mod_cast Nat.zero_le t) zero_le_one
  · rw [ht, (Tval_closed t).2]

/-- The alternating convolution `∑ Wᵢ (-1)ᵏ⁻ⁱ W_{k-i} ≥ 0` for `c ∈ {0,1,-1}` and
`W i = ∑_{r<i+1} cʳ` (the geometric partial sums that arise as `zetaMul χ₁` values). -/
lemma altconv_nonneg (W : ℕ → ℂ) (c : ℂ) (hc : c = 0 ∨ c = 1 ∨ c = -1)
    (hW : ∀ i, W i = ∑ r ∈ Finset.range (i + 1), c ^ r) (k : ℕ) :
    0 ≤ ∑ i ∈ Finset.range (k + 1), W i * (-1) ^ (k - i) * W (k - i) := by
  rcases hc with rfl | rfl | rfl
  · -- c = 0 : W i = 1
    have hW1 : ∀ i, W i = 1 := by
      intro i; rw [hW i, Finset.sum_range_succ' _ i]; simp
    simp only [hW1, one_mul, mul_one]
    rw [← Finset.sum_range_reflect (fun i => (-1 : ℂ) ^ (k - i)) (k + 1)]
    have : ∀ i ∈ Finset.range (k + 1), (-1 : ℂ) ^ (k - (k + 1 - 1 - i)) = (-1) ^ i := by
      intro i hi
      have hik : i < k + 1 := Finset.mem_range.mp hi
      have : k - (k + 1 - 1 - i) = i := by omega
      rw [this]
    rw [Finset.sum_congr rfl this, neg_one_geom_sum]
    split_ifs <;> simp
  · -- c = 1 : W i = i + 1
    have hW1 : ∀ i, W i = (i : ℂ) + 1 := by
      intro i; rw [hW i]; simp [one_pow, Finset.sum_const, Finset.card_range]
    simp only [hW1]
    exact altconv_one k
  · -- c = -1 : each term is nonnegative
    have hWnn : ∀ j, (0 : ℂ) ≤ W j := by
      intro j; rw [hW j, neg_one_geom_sum]; split_ifs <;> simp
    refine Finset.sum_nonneg fun i hi => ?_
    rcases Nat.even_or_odd (k - i) with he | ho
    · rw [he.neg_one_pow, mul_one]
      exact mul_nonneg (hWnn i) (hWnn (k - i))
    · have h0 : W (k - i) = 0 := by rw [hW (k - i), neg_one_geom_sum, if_pos ho.add_one]
      rw [h0]; simp

/-- Nonnegativity of `fourfoldCoeff` at a prime power. -/
lemma fourfoldCoeff_prime_pow_nonneg {χ₁ χ₂ : DirichletCharacter ℂ N}
    (hχ₁ : χ₁ ^ 2 = 1) (hχ₂ : χ₂ ^ 2 = 1) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 ≤ fourfoldCoeff χ₁ χ₂ (p ^ k) := by
  rw [fourfoldCoeff_prime_pow χ₁ χ₂ hp]
  rcases quadratic_apply_mem hχ₂ p with hb | hb | hb
  · rw [hb]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (zetaMul_nonneg hχ₁ _) (pow_nonneg (le_refl 0) _))
        (zetaMul_nonneg hχ₁ _)
  · rw [hb]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (zetaMul_nonneg hχ₁ _) (pow_nonneg zero_le_one _))
        (zetaMul_nonneg hχ₁ _)
  · rw [hb]
    exact altconv_nonneg (fun i => zetaMul χ₁ (p ^ i)) (χ₁ p) (quadratic_apply_mem hχ₁ p)
      (fun i => zetaMul_prime_pow_eq χ₁ hp i) k

/-- **Deliverable 2.** The Dirichlet coefficients of `F = ζ·L(χ₁)·L(χ₂)·L(χ₁χ₂)` are nonnegative
for real characters `χ₁, χ₂`. Together with `fourfoldCoeff_apply_one` this is the exact positivity
input consumed by Goldfeld's argument (via `LSeries.positive_of_differentiable_of_eqOn`). -/
theorem fourfoldCoeff_nonneg {χ₁ χ₂ : DirichletCharacter ℂ N}
    (hχ₁ : χ₁ ^ 2 = 1) (hχ₂ : χ₂ ^ 2 = 1) (n : ℕ) :
    0 ≤ fourfoldCoeff χ₁ χ₂ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [(isMultiplicative_fourfoldCoeff χ₁ χ₂).multiplicative_factorization _ hn]
    exact Finset.prod_nonneg fun p hp =>
      fourfoldCoeff_prime_pow_nonneg hχ₁ hχ₂ (Nat.prime_of_mem_primeFactors hp) _

variable [NeZero N]

/-- Auxiliary: the L-series of `toArithmeticFunction (χ ·)` is summable on `Re s > 1`. -/
lemma LSeriesSummable_toArithmeticFunction (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (toArithmeticFunction (χ ·)) s :=
  (LSeriesSummable_congr _ fun h ↦ (χ.apply_eq_toArithmeticFunction_apply h).symm).mpr <|
    ZMod.LSeriesSummable_of_one_lt_re χ hs

/-- Auxiliary: the L-series of `toArithmeticFunction (χ ·)` equals `LFunction χ` on `Re s > 1`. -/
lemma LSeries_toArithmeticFunction_eq (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries (toArithmeticFunction (χ ·)) s = LFunction χ s := by
  rw [χ.LFunction_eq_LSeries hs]
  exact LSeries_congr (fun h ↦ (χ.apply_eq_toArithmeticFunction_apply h).symm) s

/-- The L-series of `fourfoldCoeff` converges for `Re s > 1`. -/
lemma LSeriesSummable_fourfoldCoeff (χ₁ χ₂ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fourfoldCoeff χ₁ χ₂) s :=
  ArithmeticFunction.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_mul (LSeriesSummable_zetaMul χ₁ hs)
      (LSeriesSummable_toArithmeticFunction χ₂ hs))
    (LSeriesSummable_toArithmeticFunction (χ₁ * χ₂) hs)

/-- The L-series of `zetaMul χ` is `ζ(s)·L(s,χ)` on `Re s > 1` (the 2-fold building block). -/
lemma LSeries_zetaMul_eq (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries (zetaMul χ) s = riemannZeta s * LFunction χ s := by
  rw [zetaMul, ← coe_mul, LSeries_convolution']
  · rw [LSeries_toArithmeticFunction_eq χ hs]
    congr 1
    rw [← LSeries_zeta_eq_riemannZeta hs]
    exact LSeries_congr (fun _ ↦ natCoe_apply) s
  · exact LSeriesSummable_zeta_iff.mpr hs
  · exact LSeriesSummable_toArithmeticFunction χ hs

/-- **The L-series product identity.** On `Re s > 1`,
`LSeries (fourfoldCoeff χ₁ χ₂) s = ζ(s)·L(s,χ₁)·L(s,χ₂)·L(s,χ₁χ₂)`. -/
theorem LSeries_fourfoldCoeff_eq (χ₁ χ₂ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fourfoldCoeff χ₁ χ₂) s
      = riemannZeta s * LFunction χ₁ s * LFunction χ₂ s * LFunction (χ₁ * χ₂) s := by
  have h12 := LSeriesSummable_toArithmeticFunction (χ₁ * χ₂) hs
  have h2 := LSeriesSummable_toArithmeticFunction χ₂ hs
  have hz := LSeriesSummable_zetaMul χ₁ hs
  rw [fourfoldCoeff,
    ArithmeticFunction.LSeries_mul' (ArithmeticFunction.LSeriesSummable_mul hz h2) h12,
    ArithmeticFunction.LSeries_mul' hz h2,
    LSeries_zetaMul_eq χ₁ hs, LSeries_toArithmeticFunction_eq χ₂ hs,
    LSeries_toArithmeticFunction_eq (χ₁ * χ₂) hs]

/-! ## 4. The `changeLevel` packaging -/

/-- `changeLevel` preserves the quadratic property. -/
lemma changeLevel_quadratic {q m : ℕ} (hm : q ∣ m) {χ : DirichletCharacter ℂ q}
    (hχ : χ ^ 2 = 1) : (changeLevel (R := ℂ) hm χ) ^ 2 = 1 := by
  rw [← map_pow, hχ, map_one]

end Salt.SW

end




section
open Complex DirichletCharacter ArithmeticFunction
open scoped LSeries.notation ComplexOrder ArithmeticFunction ArithmeticFunction.zeta
variable {N : ℕ}
variable [NeZero N]

theorem solution (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries (toArithmeticFunction (χ ·)) s = LFunction χ s := by
  apply Salt.SW.LSeries_toArithmeticFunction_eq <;> assumption

end

