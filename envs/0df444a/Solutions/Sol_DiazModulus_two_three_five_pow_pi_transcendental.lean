-- Prove2me | solution 1 for DiazModulus.two_three_five_pow_pi_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T16:33:45.723503+00:00
-- url     : https://prove2.me/submissions/d2a7b3ab-6ad7-4633-a885-3956700c6a2b

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_six_exponentials

namespace PowPi

/-- The `p`-adic valuation of `2^A 3^B 5^C`. -/
theorem val_eq (p : ℕ) [Fact p.Prime] (A B C : ℤ)
    (h : ((2 : ℕ) : ℚ) ^ A * ((3 : ℕ) : ℚ) ^ B * ((5 : ℕ) : ℚ) ^ C = 1) :
    A * (padicValNat p 2 : ℤ) + B * padicValNat p 3 + C * padicValNat p 5 = 0 := by
  have h2 : ((2 : ℕ) : ℚ) ≠ 0 := by norm_num
  have h3 : ((3 : ℕ) : ℚ) ≠ 0 := by norm_num
  have h5 : ((5 : ℕ) : ℚ) ≠ 0 := by norm_num
  have := congrArg (padicValRat p) h
  rw [padicValRat.mul (mul_ne_zero (zpow_ne_zero _ h2) (zpow_ne_zero _ h3)) (zpow_ne_zero _ h5),
    padicValRat.mul (zpow_ne_zero _ h2) (zpow_ne_zero _ h3),
    padicValRat.zpow _, padicValRat.zpow _, padicValRat.zpow _,
    padicValRat.of_nat, padicValRat.of_nat, padicValRat.of_nat, padicValRat.one] at this
  exact this

/-- `2^A 3^B 5^C = 1` forces `A = B = C = 0`. -/
theorem exps_zero (A B C : ℤ)
    (h : ((2 : ℕ) : ℚ) ^ A * ((3 : ℕ) : ℚ) ^ B * ((5 : ℕ) : ℚ) ^ C = 1) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have e2 := val_eq 2 A B C h
  have e3 := val_eq 3 A B C h
  have e5 := val_eq 5 A B C h
  have v22 : padicValNat 2 2 = 1 := padicValNat.self (by norm_num)
  have v33 : padicValNat 3 3 = 1 := padicValNat.self (by norm_num)
  have v55 : padicValNat 5 5 = 1 := padicValNat.self (by norm_num)
  have v23 : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have v25 : padicValNat 2 5 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have v32 : padicValNat 3 2 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have v35 : padicValNat 3 5 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have v52 : padicValNat 5 2 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have v53 : padicValNat 5 3 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [v22, v23, v25] at e2
  rw [v32, v33, v35] at e3
  rw [v52, v53, v55] at e5
  simp at e2 e3 e5
  exact ⟨e2, e3, e5⟩

/-- `log 2`, `log 3`, `log 5` are linearly independent over `ℚ`. -/
theorem logs_indep (a b c : ℚ)
    (h : (a : ℝ) * Real.log 2 + b * Real.log 3 + c * Real.log 5 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  set A : ℤ := a.num * (b.den * c.den) with hA
  set B : ℤ := b.num * (a.den * c.den) with hB
  set C : ℤ := c.num * (a.den * b.den) with hC
  have hD : (0 : ℝ) < (a.den : ℝ) * b.den * c.den := by positivity
  have hAr : (A : ℝ) = a * ((a.den : ℝ) * b.den * c.den) := by
    rw [hA, Rat.cast_def a]; push_cast
    have : (a.den : ℝ) ≠ 0 := by exact_mod_cast a.den_nz
    field_simp
  have hBr : (B : ℝ) = b * ((a.den : ℝ) * b.den * c.den) := by
    rw [hB, Rat.cast_def b]; push_cast
    have : (b.den : ℝ) ≠ 0 := by exact_mod_cast b.den_nz
    field_simp
  have hCr : (C : ℝ) = c * ((a.den : ℝ) * b.den * c.den) := by
    rw [hC, Rat.cast_def c]; push_cast
    have : (c.den : ℝ) ≠ 0 := by exact_mod_cast c.den_nz
    field_simp
  have hZ : (A : ℝ) * Real.log 2 + B * Real.log 3 + C * Real.log 5 = 0 := by
    rw [hAr, hBr, hCr]; linear_combination ((a.den : ℝ) * b.den * c.den) * h
  -- exponentiate
  have hprod : ((2 : ℝ) ^ A * (3 : ℝ) ^ B * (5 : ℝ) ^ C) = 1 := by
    have e := congrArg Real.exp hZ
    rw [Real.exp_zero, Real.exp_add, Real.exp_add] at e
    rw [← e, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_intCast,
      Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos (by norm_num),
      Real.rpow_def_of_pos (by norm_num)]
    ring_nf
  have hq : ((2 : ℕ) : ℚ) ^ A * ((3 : ℕ) : ℚ) ^ B * ((5 : ℕ) : ℚ) ^ C = 1 := by
    have : ((((2 : ℕ) : ℚ) ^ A * ((3 : ℕ) : ℚ) ^ B * ((5 : ℕ) : ℚ) ^ C : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by
      push_cast; exact hprod
    exact_mod_cast this
  obtain ⟨hA0, hB0, hC0⟩ := exps_zero A B C hq
  refine ⟨?_, ?_, ?_⟩
  · have : a.num = 0 := by
      rw [hA] at hA0
      rcases mul_eq_zero.1 hA0 with h | h
      · exact h
      · exfalso; have := mul_ne_zero (b.den_nz) (c.den_nz); exact_mod_cast this (by exact_mod_cast h)
    exact Rat.num_eq_zero.1 this
  · have : b.num = 0 := by
      rw [hB] at hB0
      rcases mul_eq_zero.1 hB0 with h | h
      · exact h
      · exfalso; have := mul_ne_zero (a.den_nz) (c.den_nz); exact_mod_cast this (by exact_mod_cast h)
    exact Rat.num_eq_zero.1 this
  · have : c.num = 0 := by
      rw [hC] at hC0
      rcases mul_eq_zero.1 hC0 with h | h
      · exact h
      · exfalso; have := mul_ne_zero (a.den_nz) (b.den_nz); exact_mod_cast this (by exact_mod_cast h)
    exact Rat.num_eq_zero.1 this

theorem alg_real_to_complex {x : ℝ} (h : IsAlgebraic ℚ x) : IsAlgebraic ℚ ((x : ℝ) : ℂ) := by
  simpa using h.algebraMap (A := ℂ)

theorem alg_exp_log (p : ℕ) (hp : 0 < p) :
    IsAlgebraic ℚ (Complex.exp (((Real.log p : ℝ)) : ℂ)) := by
  rw [← Complex.ofReal_exp, Real.exp_log (by exact_mod_cast hp)]
  simpa using (isAlgebraic_algebraMap (p : ℚ) : IsAlgebraic ℚ (algebraMap ℚ ℂ p))

theorem alg_exp_pi_log (p : ℕ) (hp : 0 < p) (h : IsAlgebraic ℚ ((p : ℝ) ^ Real.pi)) :
    IsAlgebraic ℚ (Complex.exp (((Real.pi : ℝ) : ℂ) * ((Real.log p : ℝ) : ℂ))) := by
  have : ((p : ℝ) ^ Real.pi) = Real.exp (Real.pi * Real.log p) := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast hp), mul_comm]
  rw [this] at h
  have h' := alg_real_to_complex h
  rwa [Complex.ofReal_exp, Complex.ofReal_mul] at h'

end PowPi

open PowPi in
/-- The six exponentials theorem at `x = (1, π)` and `y = (log 2, log 3, log 5)`. -/
theorem solution :
    Transcendental ℚ ((2 : ℝ) ^ Real.pi) ∨ Transcendental ℚ ((3 : ℝ) ^ Real.pi) ∨
      Transcendental ℚ ((5 : ℝ) ^ Real.pi) := by
  by_contra h
  simp only [not_or, Transcendental, not_not] at h
  obtain ⟨h2, h3, h5⟩ := h
  have hx : LinearIndependent ℚ ![(1 : ℂ), ((Real.pi : ℝ) : ℂ)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hc : ((s : ℝ) + (t : ℝ) * Real.pi : ℝ) = 0 := by
      have := congrArg Complex.re hst
      simpa [Rat.smul_def] using this
    by_cases ht : t = 0
    · subst ht; simp at hc; exact ⟨by exact_mod_cast hc, rfl⟩
    · exfalso
      refine irrational_pi ⟨-s / t, ?_⟩
      have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht
      push_cast
      field_simp
      linarith
  have hy : LinearIndependent ℚ
      ![((Real.log 2 : ℝ) : ℂ), ((Real.log 3 : ℝ) : ℂ), ((Real.log 5 : ℝ) : ℂ)] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    have hr : ((g 0 : ℝ) * Real.log 2 + g 1 * Real.log 3 + g 2 * Real.log 5 : ℝ) = 0 := by
      have h' : (((g 0 : ℝ) * Real.log 2 + g 1 * Real.log 3 + g 2 * Real.log 5 : ℝ) : ℂ)
          = ((0 : ℝ) : ℂ) := by
        rw [Complex.ofReal_zero, ← hg]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, Rat.smul_def]
        push_cast
        ring
      exact_mod_cast h'
    obtain ⟨h0, h1, h2'⟩ := logs_indep (g 0) (g 1) (g 2) hr
    intro i
    fin_cases i <;> assumption
  obtain ⟨i, j, hij⟩ := DiazModulus.six_exponentials _ _ hx hy
  have hlog : ∀ p : ℕ, 0 < p →
      IsAlgebraic ℚ (Complex.exp (1 * ((Real.log p : ℝ) : ℂ))) := by
    intro p hp; rw [one_mul]; exact alg_exp_log p hp
  fin_cases i <;> fin_cases j
  · exact hij (by simpa using hlog 2 (by norm_num))
  · exact hij (by simpa using hlog 3 (by norm_num))
  · exact hij (by simpa using hlog 5 (by norm_num))
  · exact hij (by simpa using alg_exp_pi_log 2 (by norm_num) (by exact_mod_cast h2))
  · exact hij (by simpa using alg_exp_pi_log 3 (by norm_num) (by exact_mod_cast h3))
  · exact hij (by simpa using alg_exp_pi_log 5 (by norm_num) (by exact_mod_cast h5))

#print axioms solution
