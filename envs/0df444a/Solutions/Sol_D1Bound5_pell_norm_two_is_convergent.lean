-- Prove2me | solution 1 for D1Bound5.pell_norm_two_is_convergent
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:35:16.021642+00:00
-- url     : https://prove2.me/submissions/70ce2f7f-43e9-4ab2-b054-d372efafec09

import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Theorems.Thm_D1Bound5_pell_norm_two_coprime

section
namespace D1Bound5



















/-- The norm-two equation gives the strict Legendre approximation, including
the reduced denominator. This is an actual Pell theorem, not an assumed
continued-fraction enumeration. -/
theorem _root_.solution {d x y : ℤ} (hd : 7 ≤ d)
    (hx : 0 < x) (hy : 0 < y) (heq : x^2-d*y^2=2) :
    ∃ n, (x/y : ℚ) = (Real.sqrt (d : ℝ)).convergent n := by
  have hcop := pell_norm_two_coprime hx heq
  have hcop' := Int.isCoprime_iff_nat_coprime.mp hcop
  have hden := Rat.den_div_eq_of_coprime hy hcop'
  have hd0 : (0 : ℝ) ≤ d := by exact_mod_cast (show 0 ≤ d by omega)
  have hs := Real.sq_sqrt hd0
  have hs0 := Real.sqrt_nonneg (d : ℝ)
  have hs2 : (2 : ℝ) < Real.sqrt d := by
    have hd' : (7 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have heq' : (x : ℝ)^2-d*(y : ℝ)^2=2 := by exact_mod_cast heq
  have hsY : (Real.sqrt (d : ℝ)*y)^2 = d*(y : ℝ)^2 := by
    rw [mul_pow,hs]
  have hxy : Real.sqrt d * y < x := by nlinarith [sq_nonneg (Real.sqrt d*y)]
  have hdiff : |Real.sqrt (d : ℝ) - (x : ℝ)/y| =
      2 / ((y : ℝ) * (x+Real.sqrt d*y)) := by
    rw [abs_of_neg (sub_neg.mpr ((lt_div_iff₀ hy').mpr hxy))]
    have hh : (x : ℝ)+Real.sqrt d*y ≠ 0 := by positivity
    field_simp [hy'.ne', hh]
    nlinarith
  have happrox : |Real.sqrt (d : ℝ) - (x : ℝ)/y| <
      1 / (2*(y : ℝ)^2) := by
    rw [hdiff]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    have hsprod : 2*(y : ℝ) < Real.sqrt d*y := mul_lt_mul_of_pos_right hs2 hy'
    nlinarith [mul_lt_mul_of_pos_left hxy hy',mul_lt_mul_of_pos_left hsprod hy']
  apply Real.exists_rat_eq_convergent
  have hden' : (((x/y : ℚ).den : ℕ) : ℝ) = y := by exact_mod_cast hden
  simpa only [Rat.cast_div, Rat.cast_intCast, hden'] using happrox



end D1Bound5
end
