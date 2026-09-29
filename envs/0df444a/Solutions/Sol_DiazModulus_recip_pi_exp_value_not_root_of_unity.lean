-- Prove2me | solution 1 for DiazModulus.recip_pi_exp_value_not_root_of_unity
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-09T06:56:40.162351+00:00
-- url     : https://prove2.me/submissions/3f32a319-3f73-41d1-803b-437377775778

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_pi_sq_transcendental

open Complex ComplexConjugate

namespace DiazModulus

/-- Step toward `(S)` / `real_gamma`: the value of `exp (γ / (π * I))` at a
    nonzero algebraic `γ` is never a root of unity. A root-of-unity value
    would force `π ^ 2` algebraic (or `γ = 0`). Takes `π²`-transcendence as
    an explicit hypothesis — it is Proved on-platform
    (`pi_sq_transcendental`, `e40596e3`), whose local stub is `sorry`, so it
    is assumed, not imported, keeping this file `sorry`-free. No axis
    hypothesis is needed — the computation never uses reality of `γ`.
    Local only. -/
theorem XX_recip_pi_exp_value_not_root_of_unity (γ : ℂ)
    (hγ : IsAlgebraic ℚ γ) (hne : γ ≠ 0)
    (hpi : Transcendental ℚ ((Real.pi ^ 2 : ℝ) : ℂ)) :
    ¬ IsOfFinOrder (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by
  set P : ℂ := ((Real.pi : ℝ) : ℂ) with hP
  set lam : ℂ := γ / (P * Complex.I) with hlam
  have hP0 : P ≠ 0 := by
    rw [hP]
    exact_mod_cast Real.pi_ne_zero
  have hPI : P * Complex.I ≠ 0 := mul_ne_zero hP0 Complex.I_ne_zero
  intro hfin
  obtain ⟨n, hn0, hnpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  have hexp1 : Complex.exp ((n : ℂ) * lam) = 1 := by
    rw [Complex.exp_nat_mul]
    exact hnpow
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hexp1
  rw [hlam, ← hP, ← mul_div_assoc] at hk
  -- hk : ↑n * γ / (P * I) = ↑k * (2 * P * I)
  have hcleared : (n : ℂ) * γ = (k : ℂ) * (2 * P * Complex.I) * (P * Complex.I) :=
    (div_eq_iff hPI).mp hk
  have key : (n : ℂ) * γ = -((2 * (k : ℂ)) * (P ^ 2)) := by
    linear_combination hcleared + (2 * (k : ℂ) * P ^ 2) * Complex.I_mul_I
  rcases eq_or_ne k 0 with rfl | hk0
  · have h0 : (n : ℂ) * γ = 0 := by
      rw [Int.cast_zero, mul_zero, zero_mul, neg_zero] at key
      exact key
    rcases mul_eq_zero.mp h0 with hc | hγ0
    · exact absurd (Nat.cast_eq_zero.mp hc) (ne_of_gt hn0)
    · exact hne hγ0
  · have hkC : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hk0
    have h2k : (2 : ℂ) * (k : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hkC
    have hP2alg : IsAlgebraic ℚ (P ^ 2) := by
      have hmem : P ^ 2 = (-((n : ℂ) * γ)) / (2 * (k : ℂ)) := by
        rw [eq_div_iff h2k]
        linear_combination key
      rw [hmem, div_eq_mul_inv]
      exact IsAlgebraic.mul (IsAlgebraic.neg (IsAlgebraic.mul (isAlgebraic_natCast n) hγ))
        (IsAlgebraic.inv (IsAlgebraic.mul (isAlgebraic_natCast 2) (isAlgebraic_intCast k)))
    have hcast : ((Real.pi ^ 2 : ℝ) : ℂ) = P ^ 2 := by
      rw [hP, Complex.ofReal_pow]
    rw [← hcast] at hP2alg
    exact hpi hP2alg

end DiazModulus


open DiazModulus in
theorem solution :
    ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 →
      ¬ IsOfFinOrder (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) :=
  fun γ hγ hne =>
    DiazModulus.XX_recip_pi_exp_value_not_root_of_unity γ hγ hne
      DiazModulus.pi_sq_transcendental
