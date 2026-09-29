-- Prove2me | solution 1 for DiazModulus.torsion_rational_modulus_unique
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-29T06:36:18.0528+00:00
-- url     : https://prove2.me/submissions/90a6d908-8970-40c6-af5a-d51e872a3bed

import Mathlib
import Theorems.Thm_DiazModulus_nongeneric_rational_modulus_orbit

/-!
# Uniqueness of the torsion pair at a rational squared modulus

Let `t₀, t₁` be real with `e^{t₀}, e^{t₁}` algebraic and `t_k² + π² = r_k` rational. Put
`u = t₀ + π i` and `v = t₁ + π i`.

* Both are non-zero, since their imaginary parts equal `π`.
* `e^u = -e^{t₀}` and `e^v = -e^{t₁}` are algebraic.
* `u * conj u = t₀² + π² = r₀` and `v * conj v = t₁² + π² = r₁`.
* Over `A = ℚ[π]`: `t_k² = r_k - π²` lies in `A`, so `t_k` is algebraic over `A`; `i² = -1`, so
  `i` is algebraic over `A`; hence `u` and `v` are algebraic over `A`.

The rational-modulus orbit statement gives `q ∈ ℚ` with `v = q u` or `v = q conj u`. Comparing
imaginary parts forces `q = 1` in the first case and `q = -1` in the second, and comparing real
parts then gives `t₁ = t₀` or `t₁ = -t₀`.
-/

open ComplexConjugate

namespace R1_torsion_rational_modulus_unique

/-- The subalgebra `ℚ[π]` of `ℂ`. -/
noncomputable abbrev Api : Subalgebra ℚ ℂ := Algebra.adjoin ℚ ({((Real.pi : ℝ) : ℂ)} : Set ℂ)

/-- `π` is algebraic over `ℚ[π]`. -/
theorem isAlgebraic_pi : IsAlgebraic Api ((Real.pi : ℝ) : ℂ) := by
  have h := isAlgebraic_algebraMap (R := Api) (A := ℂ)
    (⟨((Real.pi : ℝ) : ℂ), Algebra.subset_adjoin (Set.mem_singleton _)⟩ : Api)
  exact h

/-- A rational number is algebraic over `ℚ[π]`. -/
theorem isAlgebraic_ratCast (r : ℚ) : IsAlgebraic Api (r : ℂ) := by
  have h := isAlgebraic_algebraMap (R := Api) (A := ℂ) (algebraMap ℚ Api r)
  have e : algebraMap Api ℂ (algebraMap ℚ Api r) = (r : ℂ) := by
    rw [← IsScalarTower.algebraMap_apply ℚ Api ℂ r, eq_ratCast (algebraMap ℚ ℂ) r]
  rwa [e] at h

/-- `i` is algebraic over `ℚ[π]`, being a root of `X² + 1`. -/
theorem isAlgebraic_I : IsAlgebraic Api Complex.I := by
  refine IsAlgebraic.of_pow (n := 2) two_pos ?_
  rw [Complex.I_sq]
  exact (isAlgebraic_one (R := Api) (A := ℂ)).neg

/-- If `t² + π² = r` with `r` rational, then `t + π i` is algebraic over `ℚ[π]`. -/
theorem isAlgebraic_add_pi_I (t : ℝ) (r : ℚ) (hr : t ^ 2 + Real.pi ^ 2 = r) :
    IsAlgebraic Api ((t : ℂ) + ((Real.pi : ℝ) : ℂ) * Complex.I) := by
  have hsq : (t : ℂ) ^ 2 = (r : ℂ) - ((Real.pi : ℝ) : ℂ) ^ 2 := by
    have h : ((t ^ 2 + Real.pi ^ 2 : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by rw [hr]
    rw [Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_pow,
      Complex.ofReal_ratCast] at h
    rw [← h, add_sub_cancel_right]
  have ht : IsAlgebraic Api (t : ℂ) := by
    refine IsAlgebraic.of_pow (n := 2) two_pos ?_
    rw [hsq]
    exact (isAlgebraic_ratCast r).sub (isAlgebraic_pi.pow 2)
  exact ht.add (isAlgebraic_pi.mul isAlgebraic_I)

/-- `e^{t + π i} = -e^t`, so it is algebraic when `e^t` is. -/
theorem isAlgebraic_exp_add_pi_I (t : ℝ) (he : IsAlgebraic ℚ (Complex.exp (t : ℂ))) :
    IsAlgebraic ℚ (Complex.exp ((t : ℂ) + ((Real.pi : ℝ) : ℂ) * Complex.I)) := by
  rw [Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]
  exact he.neg

/-- `(t + π i) * conj (t + π i) = t² + π²`. -/
theorem mul_conj_add_pi_I (t : ℝ) (r : ℚ) (hr : t ^ 2 + Real.pi ^ 2 = r) :
    ((t : ℂ) + ((Real.pi : ℝ) : ℂ) * Complex.I) *
      conj ((t : ℂ) + ((Real.pi : ℝ) : ℂ) * Complex.I) = (r : ℂ) := by
  have h : ((t ^ 2 + Real.pi ^ 2 : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by rw [hr]
  rw [Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_pow,
    Complex.ofReal_ratCast] at h
  rw [← h, map_add (starRingEnd ℂ), map_mul (starRingEnd ℂ), Complex.conj_ofReal,
    Complex.conj_ofReal, Complex.conj_I]
  linear_combination (-((Real.pi : ℝ) : ℂ) ^ 2) * Complex.I_sq

/-- `t + π i ≠ 0`, since its imaginary part is `π`. -/
theorem add_pi_I_ne_zero (t : ℝ) : (t : ℂ) + ((Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, Complex.zero_im, mul_zero, mul_one, zero_add, add_zero] at him
  exact Real.pi_ne_zero him

end R1_torsion_rational_modulus_unique

open R1_torsion_rational_modulus_unique in
theorem solution (t₀ t₁ : ℝ)
    (he₀ : IsAlgebraic ℚ (Complex.exp (t₀ : ℂ))) (he₁ : IsAlgebraic ℚ (Complex.exp (t₁ : ℂ)))
    (r₀ r₁ : ℚ) (hr₀ : t₀ ^ 2 + Real.pi ^ 2 = r₀) (hr₁ : t₁ ^ 2 + Real.pi ^ 2 = r₁) :
    t₁ = t₀ ∨ t₁ = -t₀ := by
  obtain ⟨q, hq | hq⟩ := DiazModulus.nongeneric_rational_modulus_orbit
    ((t₀ : ℂ) + ((Real.pi : ℝ) : ℂ) * Complex.I) ((t₁ : ℂ) + ((Real.pi : ℝ) : ℂ) * Complex.I)
    (add_pi_I_ne_zero t₀) (add_pi_I_ne_zero t₁)
    (isAlgebraic_exp_add_pi_I t₀ he₀) (isAlgebraic_exp_add_pi_I t₁ he₁) r₀ r₁
    (mul_conj_add_pi_I t₀ r₀ hr₀) (mul_conj_add_pi_I t₁ r₁ hr₁)
    (isAlgebraic_add_pi_I t₀ r₀ hr₀) (isAlgebraic_add_pi_I t₁ r₁ hr₁)
  · have hre := congrArg Complex.re hq
    have him := congrArg Complex.im hq
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.ratCast_re,
      Complex.ratCast_im, mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add] at hre him
    -- `hre : t₁ = q * t₀` and `him : π = q * π`
    have hq1 : (q : ℝ) = 1 := by
      have h : ((q : ℝ) - 1) * Real.pi = 0 := by linear_combination -him
      linear_combination (mul_eq_zero.mp h).resolve_right Real.pi_ne_zero
    left
    linear_combination hre + t₀ * hq1
  · have hre := congrArg Complex.re hq
    have him := congrArg Complex.im hq
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.ratCast_re,
      Complex.ratCast_im, Complex.conj_re, Complex.conj_im, mul_zero, zero_mul, mul_one,
      sub_zero, add_zero, zero_add] at hre him
    -- `hre : t₁ = q * t₀` and `him : π = q * (-π)`
    have hq1 : (q : ℝ) = -1 := by
      have h : ((q : ℝ) + 1) * Real.pi = 0 := by linear_combination him
      linear_combination (mul_eq_zero.mp h).resolve_right Real.pi_ne_zero
    right
    linear_combination hre + t₀ * hq1
