-- Prove2me | solution 1 for DiazModulus.aligned_norm_free_no_quadratic_relation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:36:55.121762+00:00
-- url     : https://prove2.me/submissions/6aa4f67f-c482-48aa-8673-f9a429687af2

import Mathlib
import Theorems.Thm_Transcendence_quadratic_coeffs_eq_zero_of_transcendental
import Theorems.Thm_DiazModulus_pi_transcendental

/-!
Write `u = t + iy`, `β = π(y + rπ)` and `ρ = |u|² = t² + y²`. A rational quadratic form in
`(u, ū, 2πi)` depends only on its diagonal coefficients `a, b, c` and on its symmetrised
off-diagonal coefficients `d, e, f` (of `uū`, `u·2πi` and `ū·2πi`). At `(u, ū, 2πi)` its imaginary
part is `2t((a - b)y + (e + f)π)` and its real part is
`(a + b)(t² - y²) + d(t² + y²) - 4cπ² + 2(f - e)πy`.

Multiply the first by `π/(2t)` and the second by `π²`, then eliminate `t²` with `t² = ρ - y²` and
`πy` with `πy = β - rπ²`. Both become polynomials in `π²` whose coefficients are algebraic, so
all coefficients vanish, since `π²` is transcendental. Every resulting condition is rational
linear algebra except one: `(a + b + d)ρ + (4(a + b)r + 2(f - e))β = 0`. If `a + b + d ≠ 0`, this
puts `ρ` in `ℚβ`, which is excluded. So all six coefficients vanish, which says exactly that the
coefficient matrix is alternating.
-/

namespace S7W2_aligned_norm_free_no_quadratic_relation

/-- A rational number, viewed in `ℂ` through `ℝ`, is algebraic. -/
theorem alg_rat (q : ℚ) : IsAlgebraic ℚ (((q : ℝ)) : ℂ) := by
  rw [Complex.ofReal_ratCast]
  exact isAlgebraic_ratCast ℚ q

/-- A real relation `c₂ (π²)² + c₁ π² + c₀ = 0` with algebraic coefficients is trivial,
because `π²` is transcendental. -/
theorem pi_sq_coeffs {c₀ c₁ c₂ : ℝ} (h₀ : IsAlgebraic ℚ (c₀ : ℂ))
    (h₁ : IsAlgebraic ℚ (c₁ : ℂ)) (h₂ : IsAlgebraic ℚ (c₂ : ℂ))
    (h : c₂ * (Real.pi ^ 2) ^ 2 + c₁ * Real.pi ^ 2 + c₀ = 0) :
    c₂ = 0 ∧ c₁ = 0 ∧ c₀ = 0 := by
  have hT : Transcendental ℚ (((Real.pi : ℝ) : ℂ) ^ 2) :=
    DiazModulus.pi_transcendental.pow (by norm_num)
  have hC : (c₂ : ℂ) * (((Real.pi : ℝ) : ℂ) ^ 2) ^ 2 + (c₁ : ℂ) * ((Real.pi : ℝ) : ℂ) ^ 2
      + (c₀ : ℂ) = 0 := by
    exact_mod_cast h
  obtain ⟨h2, h1, h0⟩ :=
    Transcendence.quadratic_coeffs_eq_zero_of_transcendental hT h₀ h₁ h₂ hC
  exact ⟨Complex.ofReal_eq_zero.mp h2, Complex.ofReal_eq_zero.mp h1,
    Complex.ofReal_eq_zero.mp h0⟩

/-- A rational multiple of a non-zero real number vanishes only if the rational does. -/
theorem rat_eq_zero_of_mul {q : ℚ} {x : ℝ} (hx : x ≠ 0) (h : (q : ℝ) * x = 0) : q = 0 := by
  rcases mul_eq_zero.mp h with h | h
  · exact Rat.cast_eq_zero.mp h
  · exact absurd h hx

/-- `X + iY = 0` with `X, Y` real forces `X = Y = 0`. -/
theorem re_im_eq_zero {X Y : ℝ} (h : (X : ℂ) + (Y : ℂ) * Complex.I = 0) : X = 0 ∧ Y = 0 := by
  rw [← Complex.mk_eq_add_mul_I] at h
  exact ⟨congrArg Complex.re h, congrArg Complex.im h⟩

/-- The core computation, for `u = t + iy`, `β = π(y + rπ)` and `ρ = t² + y²`: the quadratic
form `a u² + b ū² + c (2πi)² + d uū + e u(2πi) + f ū(2πi)` with rational coefficients vanishes
only if all six coefficients do. -/
theorem six_coeffs_eq_zero (t y β ρ : ℝ) (r a b c d e f : ℚ) (ht : t ≠ 0) (hβ0 : β ≠ 0)
    (hβdef : β = Real.pi * (y + r * Real.pi)) (hρdef : ρ = t ^ 2 + y ^ 2)
    (hβ : IsAlgebraic ℚ (β : ℂ)) (hρ : IsAlgebraic ℚ (ρ : ℂ))
    (hfree : ¬ ∃ q : ℚ, ρ = q * β)
    (h : (a : ℂ) * ((t : ℂ) + y * Complex.I) ^ 2 + (b : ℂ) * ((t : ℂ) - y * Complex.I) ^ 2
      + (c : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) ^ 2
      + (d : ℂ) * (((t : ℂ) + y * Complex.I) * ((t : ℂ) - y * Complex.I))
      + (e : ℂ) * (((t : ℂ) + y * Complex.I) * (2 * (Real.pi : ℂ) * Complex.I))
      + (f : ℂ) * (((t : ℂ) - y * Complex.I) * (2 * (Real.pi : ℂ) * Complex.I)) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 := by
  -- Split into real and imaginary parts, using `i² = -1`.
  obtain ⟨hX, hY⟩ := re_im_eq_zero
    (X := ((a : ℝ) + b) * (t ^ 2 - y ^ 2) + d * (t ^ 2 + y ^ 2) - 4 * c * Real.pi ^ 2
      - 2 * e * Real.pi * y + 2 * f * Real.pi * y)
    (Y := 2 * ((a : ℝ) - b) * t * y + 2 * ((e : ℝ) + f) * Real.pi * t) (by
      push_cast
      linear_combination h - (((a : ℂ) + b) * (y : ℂ) ^ 2 + 4 * (c : ℂ) * (Real.pi : ℂ) ^ 2
        - (d : ℂ) * (y : ℂ) ^ 2 + 2 * (e : ℂ) * (Real.pi : ℂ) * y
        - 2 * (f : ℂ) * (Real.pi : ℂ) * y) * Complex.I_sq)
  -- Imaginary part: `(a - b)y + (e + f)π = 0`, so `(e + f - (a - b)r)π² + (a - b)β = 0`.
  have hY' : ((a : ℝ) - b) * y + ((e : ℝ) + f) * Real.pi = 0 := by
    have h2 : t * (2 * (((a : ℝ) - b) * y + ((e : ℝ) + f) * Real.pi)) = 0 := by
      linear_combination hY
    rcases mul_eq_zero.mp h2 with h2 | h2
    · exact absurd h2 ht
    · linear_combination h2 / 2
  obtain ⟨-, hI1, hI0⟩ := pi_sq_coeffs (c₂ := ((0 : ℚ) : ℝ))
    (c₁ := ((e + f - (a - b) * r : ℚ) : ℝ)) (c₀ := ((a - b : ℚ) : ℝ) * β)
    (by rw [Complex.ofReal_mul]; exact (alg_rat _).mul hβ) (alg_rat _) (alg_rat _)
    (by push_cast; linear_combination Real.pi * hY' + ((a : ℝ) - b) * hβdef)
  have hab : a - b = 0 := rat_eq_zero_of_mul hβ0 hI0
  have hef : e + f - (a - b) * r = 0 := Rat.cast_eq_zero.mp hI1
  -- Real part times `π²`, with `t² = ρ - y²` and `πy = β - rπ²`:
  -- `(-2(a + b)r² - 4c - 2(f - e)r)π⁴ + ((a + b + d)ρ + (4(a + b)r + 2(f - e))β)π²
  --   - 2(a + b)β² = 0`.
  obtain ⟨hR2, hR1, hR0⟩ := pi_sq_coeffs
    (c₂ := ((-2 * (a + b) * r ^ 2 - 4 * c - 2 * (f - e) * r : ℚ) : ℝ))
    (c₁ := ((a + b + d : ℚ) : ℝ) * ρ + ((4 * (a + b) * r + 2 * (f - e) : ℚ) : ℝ) * β)
    (c₀ := ((-2 * (a + b) : ℚ) : ℝ) * β ^ 2)
    (by rw [Complex.ofReal_mul, Complex.ofReal_pow]; exact (alg_rat _).mul (hβ.pow 2))
    (by
      rw [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_mul]
      exact ((alg_rat _).mul hρ).add ((alg_rat _).mul hβ))
    (alg_rat _)
    (by
      push_cast
      linear_combination Real.pi ^ 2 * hX + ((a : ℝ) + b + d) * Real.pi ^ 2 * hρdef
        + (((a : ℝ) + b) * (4 * r * Real.pi ^ 2 - 2 * (β + Real.pi * (y + r * Real.pi)))
          + 2 * ((f : ℝ) - e) * Real.pi ^ 2) * hβdef)
  have hab' : -2 * (a + b) = 0 := rat_eq_zero_of_mul (pow_ne_zero 2 hβ0) hR0
  have hc' : -2 * (a + b) * r ^ 2 - 4 * c - 2 * (f - e) * r = 0 := Rat.cast_eq_zero.mp hR2
  -- The `π²` coefficient: if `a + b + d ≠ 0` it puts `ρ` in `ℚβ`.
  have hs : a + b + d = 0 := by
    by_contra hs
    refine hfree ⟨-(4 * (a + b) * r + 2 * (f - e)) / (a + b + d), ?_⟩
    rw [Rat.cast_div, Rat.cast_neg, div_mul_eq_mul_div, eq_div_iff (Rat.cast_ne_zero.mpr hs)]
    linear_combination hR1
  rw [hs, Rat.cast_zero, zero_mul, zero_add] at hR1
  have hk : 4 * (a + b) * r + 2 * (f - e) = 0 := rat_eq_zero_of_mul hβ0 hR1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (hab - hab' / 2) / 2
  · linear_combination (-hab' / 2 - hab) / 2
  · linear_combination (-(r ^ 2) * hab' - r * hk - hc') / 4
  · linear_combination hs + hab' / 2
  · linear_combination (hef + r * hab - (hk + 2 * r * hab') / 2) / 2
  · linear_combination (hef + r * hab + (hk + 2 * r * hab') / 2) / 2

end S7W2_aligned_norm_free_no_quadratic_relation

open ComplexConjugate in
/-- Expand the form, write `u = Re u + i Im u` and `ū = Re u - i Im u`, and apply the core
computation to the diagonal and symmetrised off-diagonal coefficients. -/
theorem solution (u : ℂ) (r : ℚ) (hre : u.re ≠ 0)
    (hβ0 : Real.pi * (u.im + (r : ℝ) * Real.pi) ≠ 0)
    (hβ : IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ))
    (hρ : IsAlgebraic ℚ ((((‖u‖ : ℝ)) ^ 2 : ℝ) : ℂ))
    (hfree : ¬ ∃ c : ℚ, (‖u‖ : ℝ) ^ 2 = (c : ℝ) * (Real.pi * (u.im + (r : ℝ) * Real.pi)))
    (F : Fin 3 → Fin 3 → ℚ)
    (h : ∑ k, ∑ l, (F k l : ℂ) *
      (![u, conj u, 2 * ((Real.pi : ℝ) : ℂ) * Complex.I] k *
        ![u, conj u, 2 * ((Real.pi : ℝ) : ℂ) * Complex.I] l) = 0) :
    ∀ k l, F k l + F l k = 0 := by
  have e0 : (![u, conj u, 2 * ((Real.pi : ℝ) : ℂ) * Complex.I] : Fin 3 → ℂ) 0 = u := rfl
  have e1 : (![u, conj u, 2 * ((Real.pi : ℝ) : ℂ) * Complex.I] : Fin 3 → ℂ) 1 = conj u := rfl
  have e2 : (![u, conj u, 2 * ((Real.pi : ℝ) : ℂ) * Complex.I] : Fin 3 → ℂ) 2
      = 2 * ((Real.pi : ℝ) : ℂ) * Complex.I := rfl
  simp only [Fin.sum_univ_three, e0, e1, e2] at h
  have hcu : conj u = (u.re : ℂ) - (u.im : ℂ) * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im u]
    rw [map_add (starRingEnd ℂ), map_mul (starRingEnd ℂ), Complex.conj_ofReal,
      Complex.conj_ofReal, Complex.conj_I]
    ring
  have hnorm : (‖u‖ : ℝ) ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  obtain ⟨ha, hb, hc, hd, he, hf⟩ :=
    S7W2_aligned_norm_free_no_quadratic_relation.six_coeffs_eq_zero u.re u.im _ _ r
      (F 0 0) (F 1 1) (F 2 2) (F 0 1 + F 1 0) (F 0 2 + F 2 0) (F 1 2 + F 2 1)
      hre hβ0 rfl hnorm hβ hρ hfree (by
        rw [← hcu, Complex.re_add_im]
        push_cast
        linear_combination h)
  have hfin : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  intro k l
  rcases hfin k with rfl | rfl | rfl <;> rcases hfin l with rfl | rfl | rfl <;> linarith

#print axioms solution
