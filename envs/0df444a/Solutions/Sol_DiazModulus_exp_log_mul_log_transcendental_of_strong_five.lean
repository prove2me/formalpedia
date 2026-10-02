-- Prove2me | solution 1 for DiazModulus.exp_log_mul_log_transcendental_of_strong_five
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T14:42:41.857346+00:00
-- url     : https://prove2.me/submissions/2b0a5b4b-735a-47cd-9166-e707684f7b8a

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_hermite_lindemann_holds

/-!
# Strong five exponentials: `e^{λμ}` is transcendental for non-zero logarithms `λ, μ`

The strong five exponentials conjecture (Waldschmidt), stated inline as `hS5`, implies that
`(log a)(log b) ≠ log c` for non-zero logarithms of algebraic numbers: `e^{λμ}` is transcendental.
At `μ = λ` this is the transcendence of `e^{λ²}`, and at `λ = πi` that of `e^{π²}`.

1. Hermite–Lindemann makes `λ` and `μ` irrational, so `1, λ` and `1 + μ, μ` are free over `ℚ`.
2. If `e^{λμ}` were algebraic, `hS5` at `x = (1, λ)`, `y = (1 + μ, μ)`, `η = 1`, `β = 0`, `α₁₁ = 1`
   and `α₁₂ = α₂₁ = α₂₂ = 0` would apply (Waldschmidt's choice): the five exponentials are `e^μ`,
   `e^μ`, `e^λ e^{λμ}`, `e^{λμ}` and `e^λ`. Its conclusion `x₂y₂ = α₂₂` reads `λμ = 0`.
3. `πi ∈ ℒ` because `e^{πi} = -1`, and `(πi)² = -π²`; `e^{π²}` is the inverse of `e^{-π²}`.
-/

open Complex ComplexConjugate

namespace DiazExpLogMulLog

open DiazModulus

/-- Hermite–Lindemann: a non-zero logarithm of an algebraic number is not rational, so `1, l` are
free over `ℚ`. -/
theorem linearIndependent_one_log {l : ℂ} (hl : l ∈ LogAlg) (hl0 : l ≠ 0) :
    LinearIndependent ℚ ![(1 : ℂ), l] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [Rat.smul_def, Rat.smul_def, mul_one] at hst
  by_cases ht : t = 0
  · refine ⟨?_, ht⟩
    rw [ht, Rat.cast_zero, zero_mul, add_zero] at hst
    exact_mod_cast hst
  · exfalso
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    have hlq : l = ((-s / t : ℚ) : ℂ) := by
      rw [Rat.cast_div, Rat.cast_neg, eq_div_iff ht']
      linear_combination hst
    exact hermite_lindemann_holds l hl0 (hlq ▸ isAlgebraic_ratCast ℚ (-s / t)) hl

/-- `1 + m, m` are free over `ℚ` for a non-zero logarithm `m`: a relation `s (1 + m) + t m = 0` is
the relation `s · 1 + (s + t) m = 0` between `1` and `m`. -/
theorem linearIndependent_one_add_log {m : ℂ} (hm : m ∈ LogAlg) (hm0 : m ≠ 0) :
    LinearIndependent ℚ ![1 + m, m] := by
  have hli := LinearIndependent.pair_iff.mp (linearIndependent_one_log hm hm0)
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [Rat.smul_def, Rat.smul_def] at hst
  have h := hli s (s + t) (by
    rw [Rat.smul_def, Rat.smul_def]
    push_cast
    linear_combination hst)
  exact ⟨h.1, by linarith [h.1, h.2]⟩

/-- `πi` is a non-zero logarithm of an algebraic number, namely `-1`. -/
theorem pi_mul_I_mem_logAlg : (Real.pi : ℂ) * I ∈ LogAlg := by
  show IsAlgebraic ℚ (Complex.exp ((Real.pi : ℂ) * I))
  rw [Complex.exp_pi_mul_I]
  exact isAlgebraic_one.neg

theorem pi_mul_I_ne_zero : (Real.pi : ℂ) * I ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) Complex.I_ne_zero

end DiazExpLogMulLog

open DiazModulus DiazExpLogMulLog in
theorem solution
    (hS5 : ∀ x₁ x₂ y₁ y₂ η α₁₁ α₁₂ α₂₁ α₂₂ β : ℂ,
      LinearIndependent ℚ ![x₁, x₂] → LinearIndependent ℚ ![y₁, y₂] →
      IsAlgebraic ℚ η → η ≠ 0 →
      IsAlgebraic ℚ α₁₁ → IsAlgebraic ℚ α₁₂ → IsAlgebraic ℚ α₂₁ → IsAlgebraic ℚ α₂₂ →
      IsAlgebraic ℚ β →
      IsAlgebraic ℚ (Complex.exp (x₁ * y₁ - α₁₁)) → IsAlgebraic ℚ (Complex.exp (x₁ * y₂ - α₁₂)) →
      IsAlgebraic ℚ (Complex.exp (x₂ * y₁ - α₂₁)) → IsAlgebraic ℚ (Complex.exp (x₂ * y₂ - α₂₂)) →
      IsAlgebraic ℚ (Complex.exp (η * x₂ / x₁ - β)) →
      x₁ * y₁ = α₁₁ ∧ x₁ * y₂ = α₁₂ ∧ x₂ * y₁ = α₂₁ ∧ x₂ * y₂ = α₂₂ ∧ η * x₂ = β * x₁) :
    (∀ l m : ℂ, l ∈ LogAlg → l ≠ 0 → m ∈ LogAlg → m ≠ 0 →
      Transcendental ℚ (Complex.exp (l * m))) ∧
    (∀ l : ℂ, l ∈ LogAlg → l ≠ 0 → Transcendental ℚ (Complex.exp (l ^ 2))) ∧
    Transcendental ℚ (Complex.exp (((Real.pi : ℝ) : ℂ) ^ 2)) := by
  have part0 : ∀ l m : ℂ, l ∈ LogAlg → l ≠ 0 → m ∈ LogAlg → m ≠ 0 →
      Transcendental ℚ (Complex.exp (l * m)) := by
    intro l m hl hl0 hm hm0 hlm
    have hel : IsAlgebraic ℚ (Complex.exp l) := hl
    have hem : IsAlgebraic ℚ (Complex.exp m) := hm
    -- the five exponentials `e^μ`, `e^μ`, `e^λ e^{λμ}`, `e^{λμ}`, `e^λ`
    have e11 : IsAlgebraic ℚ (Complex.exp (1 * (1 + m) - 1)) := by
      rw [show (1 : ℂ) * (1 + m) - 1 = m by ring]
      exact hem
    have e12 : IsAlgebraic ℚ (Complex.exp (1 * m - 0)) := by
      rw [show (1 : ℂ) * m - 0 = m by ring]
      exact hem
    have e21 : IsAlgebraic ℚ (Complex.exp (l * (1 + m) - 0)) := by
      rw [show l * (1 + m) - 0 = l + l * m by ring, Complex.exp_add]
      exact mem_Qbar_iff.mp (Qbar.mul_mem (mem_Qbar_iff.mpr hel) (mem_Qbar_iff.mpr hlm))
    have e22 : IsAlgebraic ℚ (Complex.exp (l * m - 0)) := by
      rw [sub_zero]
      exact hlm
    have e5 : IsAlgebraic ℚ (Complex.exp (1 * l / 1 - 0)) := by
      rw [show (1 : ℂ) * l / 1 - 0 = l by ring]
      exact hel
    have h := hS5 1 l (1 + m) m 1 1 0 0 0 0 (linearIndependent_one_log hl hl0)
      (linearIndependent_one_add_log hm hm0) isAlgebraic_one one_ne_zero isAlgebraic_one
      isAlgebraic_zero isAlgebraic_zero isAlgebraic_zero isAlgebraic_zero e11 e12 e21 e22 e5
    -- `x₂ y₂ = α₂₂` reads `λ μ = 0`
    exact mul_ne_zero hl0 hm0 h.2.2.2.1
  have part1 : ∀ l : ℂ, l ∈ LogAlg → l ≠ 0 → Transcendental ℚ (Complex.exp (l ^ 2)) := by
    intro l hl hl0
    rw [sq]
    exact part0 l l hl hl0 hl hl0
  refine ⟨part0, part1, fun hpi => ?_⟩
  apply part1 _ pi_mul_I_mem_logAlg pi_mul_I_ne_zero
  have hsq : ((Real.pi : ℂ) * I) ^ 2 = -(((Real.pi : ℝ) : ℂ) ^ 2) := by
    rw [mul_pow, Complex.I_sq]
    ring
  rw [hsq, Complex.exp_neg]
  exact hpi.inv
