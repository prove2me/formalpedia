-- Prove2me | solution 1 for EulerMascheroni.Arithmetic.quotient_coefficient_properties
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T13:37:50.772657+00:00
-- url     : https://prove2.me/submissions/5e40a70b-6837-4611-9995-ac97b3329317

import Definitions.Def_eulerMascheroni_factorialQuotient
set_option autoImplicit false
open EulerMascheroni.Arithmetic

lemma quotientCoeff_zero (a : ℝ) : quotientCoeff a 0 = a := by
  simp [quotientCoeff]

lemma quotientCoeff_recurrence (a : ℝ) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * quotientCoeff a (n + 1) =
      quotientCoeff a n - (-1 : ℝ)^n := by
  simp only [quotientCoeff, Finset.sum_range_succ, Nat.factorial_succ, Nat.cast_mul]
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

lemma quotientCoeff_algebraic (a : ℝ) (ha : IsAlgebraic ℚ a) (n : ℕ) :
    IsAlgebraic ℚ (quotientCoeff a n) := by
  induction n with
  | zero => simpa [quotientCoeff_zero] using ha
  | succ n ih =>
    have heq : quotientCoeff a (n+1) =
        (quotientCoeff a n - (-1 : ℝ)^n) / ((n+1 : ℕ) : ℝ) := by
      apply (eq_div_iff (by positivity)).mpr
      simpa [mul_comm] using quotientCoeff_recurrence a n
    rw [heq, div_eq_mul_inv]
    exact (ih.sub ((isAlgebraic_one (R := ℚ) (A := ℝ)).neg.pow n)).mul
      (isAlgebraic_natCast (n+1)).inv


lemma quotientCoeff_bound (a : ℝ) (n : ℕ) :
    |quotientCoeff a n| ≤ |a| + 1 := by
  induction n with
  | zero => simp [quotientCoeff_zero]
  | succ n ih =>
    have hn : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
    have heq : quotientCoeff a (n+1) =
        (quotientCoeff a n - (-1 : ℝ)^n) / ((n+1 : ℕ) : ℝ) := by
      apply (eq_div_iff hn.ne').mpr
      simpa [mul_comm] using quotientCoeff_recurrence a n
    rw [heq, abs_div, abs_of_pos hn]
    apply (div_le_iff₀ hn).mpr
    have ht : |quotientCoeff a n - (-1 : ℝ)^n| ≤ |quotientCoeff a n| + 1 := by
      simpa using abs_sub (quotientCoeff a n) ((-1 : ℝ)^n)
    by_cases hz : n = 0
    · subst n
      simp only [quotientCoeff_zero, pow_zero, Nat.cast_add, Nat.cast_zero,
        Nat.cast_one, zero_add, mul_one] at *
      exact ht
    · have hn' : (2 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ n+1)
      have hab := abs_nonneg a
      nlinarith


namespace EulerArithmeticWork
open PowerSeries

noncomputable def borelSeries (a : ℝ) : PowerSeries ℝ := PowerSeries.mk (quotientCoeff a)

lemma derivative_sub (a : ℝ) :
    PowerSeries.derivative ℝ (borelSeries a) - borelSeries a =
      PowerSeries.mk (fun n : ℕ => -(-1 : ℝ)^n) := by
  ext n
  simp only [map_sub, PowerSeries.coeff_derivative, borelSeries, PowerSeries.coeff_mk]
  have h := quotientCoeff_recurrence a n
  push_cast at h
  linear_combination h

lemma first_equation (a : ℝ) :
    (1 + PowerSeries.X) * (PowerSeries.derivative ℝ (borelSeries a) - borelSeries a) = -1 := by
  rw [derivative_sub]
  ext n
  rw [add_mul, one_mul, map_add]
  cases n with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff]
  | succ n =>
    have hx : PowerSeries.coeff (n+1) (PowerSeries.X *
        PowerSeries.mk (fun n : ℕ => -(-1 : ℝ)^n)) = -(-1 : ℝ)^n := by
      simpa using PowerSeries.coeff_X_pow_mul
        (PowerSeries.mk (fun n : ℕ => -(-1 : ℝ)^n)) 1 n
    rw [hx]
    simp [pow_succ]

lemma second_equation (a : ℝ) :
    (1 + PowerSeries.X) * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ (borelSeries a)) -
      PowerSeries.X * PowerSeries.derivative ℝ (borelSeries a) - borelSeries a = 0 := by
  have h := congrArg (PowerSeries.derivative ℝ) (first_equation a)
  simp only [Derivation.leibniz, map_sub, map_add, map_neg, PowerSeries.derivative_one,
    PowerSeries.derivative_X, zero_add, smul_eq_mul, mul_one, neg_zero] at h
  linear_combination h

lemma parameter_difference (a b : ℝ) :
    borelSeries a - borelSeries b = PowerSeries.C (a-b) * PowerSeries.exp ℝ := by
  apply PowerSeries.ext
  intro n
  rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_exp]
  simp only [borelSeries, PowerSeries.coeff_mk, quotientCoeff]
  simp only [map_div₀, map_one, map_natCast]
  ring

lemma coefficients_not_eventually_zero (a : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ quotientCoeff a n ≠ 0 := by
  by_contra h
  push Not at h
  have hh := quotientCoeff_recurrence a N
  rw [h N le_rfl, h (N+1) (by omega)] at hh
  have hn : (-1 : ℝ)^N ≠ 0 := pow_ne_zero _ (by norm_num)
  simp only [mul_zero, zero_sub, zero_eq_neg] at hh
  exact hn hh

end EulerArithmeticWork


theorem solution (a : ℝ) :
    EulerMascheroni.Arithmetic.quotientCoeff a 0 = a ∧
    ∀ n : ℕ,
      (((n+1 : ℕ) : ℝ) * EulerMascheroni.Arithmetic.quotientCoeff a (n+1) =
        EulerMascheroni.Arithmetic.quotientCoeff a n - (-1 : ℝ)^n) ∧
      |EulerMascheroni.Arithmetic.quotientCoeff a n| ≤ |a| + 1 ∧
      (IsAlgebraic ℚ a → IsAlgebraic ℚ (EulerMascheroni.Arithmetic.quotientCoeff a n)) := by
  refine ⟨quotientCoeff_zero a, fun n => ?_⟩
  exact ⟨quotientCoeff_recurrence a n, quotientCoeff_bound a n,
    fun ha => quotientCoeff_algebraic a ha n⟩

#print axioms solution
