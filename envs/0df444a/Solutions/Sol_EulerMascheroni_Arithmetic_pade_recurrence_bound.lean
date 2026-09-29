-- Prove2me | solution 1 for EulerMascheroni.Arithmetic.pade_recurrence_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T14:17:14.806741+00:00
-- url     : https://prove2.me/submissions/1733ca00-c06f-40ba-8c99-ae1187f0620f

import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology

namespace EulerGrowthWork

lemma recurrence_bound (U : ℕ → ℤ) (h0 : |U 0| ≤ 1) (h1 : |U 1| ≤ 4)
    (hU : ∀ n : ℕ, U (n+2) = (2*(n:ℤ)+4)*U (n+1) - ((n:ℤ)+1)^2*U n)
    (n : ℕ) : |U n| ≤ (4 : ℤ)^n * (n.factorial : ℤ) := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using h0
  | one => simpa using h1
  | more n ih ih' =>
    rw [hU n]
    calc
      |(2*(n:ℤ)+4)*U (n+1) - ((n:ℤ)+1)^2*U n| ≤
          |(2*(n:ℤ)+4)*U (n+1)| + |((n:ℤ)+1)^2*U n| := abs_sub _ _
      _ = (2*(n:ℤ)+4)*|U (n+1)| + ((n:ℤ)+1)^2*|U n| := by
        simp only [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*(n:ℤ)+4),
          abs_of_nonneg (sq_nonneg ((n:ℤ)+1))]
      _ ≤ (2*(n:ℤ)+4)*((4:ℤ)^(n+1)*((n+1).factorial:ℤ)) +
          ((n:ℤ)+1)^2*((4:ℤ)^n*(n.factorial:ℤ)) := by gcongr
      _ ≤ (4:ℤ)^(n+2)*((n+2).factorial:ℤ) := by
        simp only [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        have hn : (0 : ℤ) ≤ n := by positivity
        have hf : (0 : ℤ) ≤ (4:ℤ)^n*(n.factorial:ℤ) := by positivity
        nlinarith [mul_nonneg hf (show (0:ℤ) ≤ 7*(n:ℤ)^2+23*(n:ℤ)+16 by positivity)]

lemma normalized_pade_tendsto_zero (U : ℕ → ℤ) (C : ℝ) (hC : 1 ≤ C)
    (D : ℕ → ℕ) (hD : ∀ n, (D n : ℝ) ≤ C^(2*n+1))
    (hU : ∀ n, |U n| ≤ (4 : ℤ)^n*(n.factorial:ℤ)) :
    Tendsto (fun n => (D n : ℝ)*(U n : ℝ)/(n.factorial:ℝ)^2) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => C*((4*C^2)^n/(n.factorial:ℝ))) atTop (𝓝 0) := by
    simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (4*C^2)).const_mul C
  apply squeeze_zero_norm' _ hlim
  filter_upwards [] with n
  have hn : (0 : ℝ) < n.factorial := by positivity
  have hu : |(U n : ℝ)| ≤ (4 : ℝ)^n*(n.factorial:ℝ) := by exact_mod_cast hU n
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (sq_nonneg (n.factorial:ℝ))]
  calc
    (D n : ℝ)*|(U n:ℝ)|/(n.factorial:ℝ)^2 ≤
        C^(2*n+1)*((4:ℝ)^n*(n.factorial:ℝ))/(n.factorial:ℝ)^2 := by
      gcongr
      exact hD n
    _ = C*((4*C^2)^n/(n.factorial:ℝ)) := by
      rw [pow_add, pow_one, mul_pow, ← pow_mul]
      have hswap : 2*n=n*2 := by omega
      rw [hswap]
      field_simp
      <;> ring

end EulerGrowthWork


theorem solution (U : ℕ → ℤ) (h0 : |U 0| ≤ 1) (h1 : |U 1| ≤ 4)
    (hU : ∀ n : ℕ, U (n+2) = (2*(n:ℤ)+4)*U (n+1) - ((n:ℤ)+1)^2*U n)
    (n : ℕ) : |U n| ≤ (4 : ℤ)^n * (n.factorial : ℤ) := by
  exact EulerGrowthWork.recurrence_bound U h0 h1 hU n

#print axioms solution
