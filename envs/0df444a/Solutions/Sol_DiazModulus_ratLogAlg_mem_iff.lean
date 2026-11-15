-- Prove2me | solution 1 for DiazModulus.ratLogAlg_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T17:41:04.457806+00:00
-- url     : https://prove2.me/submissions/0063f62c-6193-4e7c-bbd3-6fb4a4235a8e

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The ℚ-span of 1 and ℒ is ℚ + ℒ

Here ℒ is the set of logarithms of algebraic numbers, the complex `u` with `exp u` algebraic over
`ℚ`. First, ℒ is a `ℚ`-subspace of `ℂ`: `exp 0 = 1`, `exp (u + v) = exp u · exp v`, and for an
integer `m` the number `exp (m u) = (exp u)^m` is algebraic (a power or the inverse of a power).
For `n ≥ 1`, `y = exp (u / n)` satisfies `y^n = exp u`, so `y` is algebraic and `u / n ∈ ℒ`;
writing a rational `q` as `m / n` gives `q u = m (u / n) ∈ ℒ`. Hence the `ℚ`-span of ℒ is ℒ
itself, and the `ℚ`-span of `{1} ∪ ℒ` is `ℚ·1 + ℒ`: an element `x` lies in it exactly when
`x = q + λ` with `q ∈ ℚ`, `λ ∈ ℒ`, i.e. when `x − q ∈ ℒ` for some rational `q`. -/

namespace RC5_RLA
open DiazModulus

theorem zero_mem : (0 : ℂ) ∈ LogAlg := by
  show IsAlgebraic ℚ (Complex.exp 0)
  rw [Complex.exp_zero]; exact isAlgebraic_one

theorem add_mem {x y : ℂ} (hx : x ∈ LogAlg) (hy : y ∈ LogAlg) : x + y ∈ LogAlg := by
  show IsAlgebraic ℚ (Complex.exp (x + y))
  rw [Complex.exp_add]; exact IsAlgebraic.mul hx hy

theorem div_nat_mem {x : ℂ} (hx : x ∈ LogAlg) {n : ℕ} (hn : 0 < n) : x / n ∈ LogAlg := by
  show IsAlgebraic ℚ (Complex.exp (x / n))
  refine IsAlgebraic.of_pow hn ?_
  rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hn.ne')]
  exact hx

theorem int_mul_mem {x : ℂ} (hx : x ∈ LogAlg) (m : ℤ) : (m : ℂ) * x ∈ LogAlg := by
  show IsAlgebraic ℚ (Complex.exp (m * x))
  rw [Complex.exp_int_mul]
  rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
  · rw [zpow_natCast]; exact IsAlgebraic.pow hx k
  · rw [zpow_neg, zpow_natCast, IsAlgebraic.inv_iff]; exact IsAlgebraic.pow hx k

noncomputable def LAsub : Submodule ℚ ℂ where
  carrier := LogAlg
  add_mem' := add_mem
  zero_mem' := zero_mem
  smul_mem' := fun q x hx => by
    have h : q • x = (q.num : ℂ) * (x / q.den) := by
      rw [Rat.smul_def, Rat.cast_def]; ring
    rw [h]
    exact int_mul_mem (div_nat_mem hx q.den_pos) q.num

theorem span_eq : Submodule.span ℚ LogAlg = LAsub := Submodule.span_eq LAsub

end RC5_RLA

open DiazModulus RC5_RLA in
theorem solution (x : ℂ) :
    x ∈ Submodule.span ℚ (insert (1 : ℂ) LogAlg) ↔ ∃ q : ℚ, x - (q : ℂ) ∈ LogAlg := by
  rw [Submodule.span_insert, span_eq, Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨q, rfl⟩ := Submodule.mem_span_singleton.1 hy
    refine ⟨q, ?_⟩
    have : q • (1 : ℂ) + z - (q : ℂ) = z := by rw [Rat.smul_def, mul_one]; ring
    rw [this]; exact hz
  · rintro ⟨q, hq⟩
    refine ⟨q • (1 : ℂ), Submodule.mem_span_singleton.2 ⟨q, rfl⟩, x - q, hq, ?_⟩
    rw [Rat.smul_def, mul_one]; ring
