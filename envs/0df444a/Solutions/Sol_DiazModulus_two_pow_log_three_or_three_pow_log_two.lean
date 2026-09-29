-- Prove2me | solution 1 for DiazModulus.two_pow_log_three_or_three_pow_log_two
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T18:26:50.134114+00:00
-- url     : https://prove2.me/submissions/658994ad-6321-442c-a494-b2d72f8f321b

import Mathlib
import Theorems.Thm_DiazModulus_log_square_duality

namespace TwoPowLogThree

/-- `log 2 / log 3` is not rational: `2^d = 3^n` has no solution with `d ≥ 1`. -/
theorem ratio_not_rat (q : ℚ) : Real.log 2 / Real.log 3 ≠ (q : ℝ) := by
  intro hr
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hqpos : (0 : ℝ) < q := by rw [← hr]; positivity
  have hnum : 0 < q.num := Rat.num_pos.2 (by exact_mod_cast hqpos)
  set m : ℕ := q.num.toNat with hm
  have hmnum : (m : ℤ) = q.num := Int.toNat_of_nonneg hnum.le
  have hq_eq : (q : ℝ) = (m : ℝ) / (q.den : ℝ) := by
    rw [Rat.cast_def]
    congr 1
    exact_mod_cast hmnum.symm
  have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hlin : (q.den : ℝ) * Real.log 2 = (m : ℝ) * Real.log 3 := by
    have : Real.log 2 = (m : ℝ) / (q.den : ℝ) * Real.log 3 := by
      rw [← hq_eq, ← hr]; field_simp
    rw [this]; field_simp
  have hpow : ((2 : ℝ) ^ q.den) = (3 : ℝ) ^ m := by
    have := congrArg Real.exp hlin
    rwa [← Real.log_pow, ← Real.log_pow, Real.exp_log (by positivity),
      Real.exp_log (by positivity)] at this
  have hnat : (2 ^ q.den : ℕ) = 3 ^ m := by exact_mod_cast hpow
  have hev : Even (2 ^ q.den) := (Nat.even_pow.2 ⟨even_two, q.den_nz⟩)
  have hod : Odd (3 ^ m) := Odd.pow (by decide)
  rw [hnat] at hev
  exact (Nat.not_even_iff_odd.2 hod) hev

/-- `e^{log p} = p` is algebraic. -/
theorem alg_exp_log (p : ℕ) (hp : 0 < p) :
    IsAlgebraic ℚ (Complex.exp (((Real.log p : ℝ)) : ℂ)) := by
  rw [← Complex.ofReal_exp, Real.exp_log (by exact_mod_cast hp)]
  simpa using (isAlgebraic_algebraMap (p : ℚ) : IsAlgebraic ℚ (algebraMap ℚ ℂ p))

/-- Transport of `p ^ (log p / log r)` to `exp ((log p)² / log r)` in `ℂ`. -/
theorem alg_transport (p r : ℕ) (hp : 0 < p)
    (h : IsAlgebraic ℚ ((p : ℝ) ^ (Real.log p / Real.log r))) :
    IsAlgebraic ℚ (Complex.exp (((Real.log p : ℝ) : ℂ) ^ 2 / ((Real.log r : ℝ) : ℂ))) := by
  have e : ((p : ℝ) ^ (Real.log p / Real.log r)) = Real.exp (Real.log p ^ 2 / Real.log r) := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast hp)]
    congr 1
    ring
  rw [e] at h
  have h' : IsAlgebraic ℚ (((Real.exp (Real.log p ^ 2 / Real.log r) : ℝ)) : ℂ) := by
    simpa using h.algebraMap (A := ℂ)
  rwa [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_pow] at h'

end TwoPowLogThree

open TwoPowLogThree in
/-- Log-square duality at `l = log 2`, `m = log 3`. -/
theorem solution :
    Transcendental ℚ ((2 : ℝ) ^ (Real.log 2 / Real.log 3)) ∨
      Transcendental ℚ ((3 : ℝ) ^ (Real.log 3 / Real.log 2)) := by
  by_contra h
  simp only [not_or, Transcendental, not_not] at h
  obtain ⟨h2, h3⟩ := h
  have h2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3p : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hind : LinearIndependent ℚ ![((Real.log 2 : ℝ) : ℂ), ((Real.log 3 : ℝ) : ℂ)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hr : (s : ℝ) * Real.log 2 + (t : ℝ) * Real.log 3 = 0 := by
      have h' : (((s : ℝ) * Real.log 2 + (t : ℝ) * Real.log 3 : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by
        rw [Complex.ofReal_zero, ← hst, Rat.smul_def, Rat.smul_def]
        push_cast
        ring
      exact_mod_cast h'
    by_cases hs : s = 0
    · subst hs
      simp only [Rat.cast_zero, zero_mul, zero_add, mul_eq_zero, Rat.cast_eq_zero] at hr
      rcases hr with ht | ht
      · exact ⟨rfl, ht⟩
      · exact absurd ht h3p.ne'
    · exfalso
      apply ratio_not_rat (-t / s)
      have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs
      push_cast
      field_simp
      linarith
  have hl := alg_exp_log 2 (by norm_num)
  have hm := alg_exp_log 3 (by norm_num)
  push_cast at hl hm
  rcases DiazModulus.log_square_duality _ _ hl hm hind with h | h
  · exact h (by exact_mod_cast alg_transport 2 3 (by norm_num) (by exact_mod_cast h2))
  · exact h (by exact_mod_cast alg_transport 3 2 (by norm_num) (by exact_mod_cast h3))

#print axioms solution
