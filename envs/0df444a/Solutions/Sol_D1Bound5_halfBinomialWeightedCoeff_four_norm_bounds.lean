-- Prove2me | solution 1 for D1Bound5.halfBinomialWeightedCoeff_four_norm_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:18:08.953526+00:00
-- url     : https://prove2.me/submissions/62ce3822-91f6-40ce-8f4b-c56bf90daed1

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentFourParameters_Definitions
import Definitions.Def_D1Bound5_ComplexHalfBinomial_Definitions
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_halfBinomialCoeff_recurrence

section
open Finset

namespace D1Bound5

private theorem halfCoeff_zero : halfBinomialCoeff 0 = 1 := by
  norm_num [halfBinomialCoeff]

private theorem halfCoeff_one : halfBinomialCoeff 1 = 1 / 2 := by
  norm_num [halfBinomialCoeff, Ring.choose_one_right]

private theorem halfCoeff_two : halfBinomialCoeff 2 = -1 / 8 := by
  have h := halfBinomialCoeff_recurrence 1
  norm_num [halfCoeff_one] at h
  linarith

private theorem halfCoeff_three : halfBinomialCoeff 3 = 1 / 16 := by
  have h := halfBinomialCoeff_recurrence 2
  norm_num [halfCoeff_two] at h
  linarith

private theorem halfCoeff_four : halfBinomialCoeff 4 = -5 / 128 := by
  have h := halfBinomialCoeff_recurrence 3
  norm_num [halfCoeff_three] at h
  linarith





/-- Frozen v4 equation (integrated-5), degree four. -/
theorem halfBinomialWeightedCoeff_four (x y : ℂ) :
    halfBinomialWeightedCoeff x y 4 =
      -(x-y)^2 * (5*x^2 + 6*x*y + 5*y^2) / 128 := by
  norm_num [halfBinomialWeightedCoeff, Finset.antidiagonal,
    halfCoeff_zero, halfCoeff_one, halfCoeff_two, halfCoeff_three, halfCoeff_four]
  ring

end D1Bound5
end
section
open Finset

noncomputable section

namespace D1Bound5













/-- The exact separated degree-four coefficient estimates. -/
theorem _root_.solution
    (x y : ℂ) (P : ℝ) (hP : 0 < P)
    (hx : ‖x‖ = 1/P) (hy : ‖y‖ ≤ 1/(1000*P)) :
    coherentFourLeadingLower/P^4 ≤ ‖halfBinomialWeightedCoeff x y 4‖ ∧
    ‖halfBinomialWeightedCoeff x y 4‖ ≤ coherentFourLeadingUpper/P^4 := by
  have hy2 : ‖y‖^2 ≤ (1/(1000*P))^2 := by gcongr
  have hDupper : ‖x-y‖ ≤ 1001/(1000*P) := by
    calc
      _ ≤ ‖x‖+‖y‖ := norm_sub_le _ _
      _ ≤ 1/P+1/(1000*P) := by rw [hx]; exact add_le_add le_rfl hy
      _ = _ := by field_simp; ring
  have hDlower : 999/(1000*P) ≤ ‖x-y‖ := by
    have h := norm_add_le (x-y) y
    rw [sub_add_cancel,hx] at h
    have heq : 1/P-1/(1000*P) = 999/(1000*P) := by field_simp; ring
    linarith only [h,hy,heq]
  have hDupper2 : ‖x-y‖^2 ≤ (1001/(1000*P))^2 := by gcongr
  have hDlower2 : (999/(1000*P))^2 ≤ ‖x-y‖^2 := by gcongr
  have hX : ‖(5:ℂ)*x^2‖ = 5/P^2 := by
    calc
      _ = 5*(1/P)^2 := by simp [norm_mul,norm_pow,hx]
      _ = _ := by field_simp <;> ring
  have hXY : ‖(6:ℂ)*x*y‖ ≤ 6/(1000*P^2) := by
    calc
      _ = 6*(1/P)*‖y‖ := by simp [norm_mul,hx]
      _ ≤ 6*(1/P)*(1/(1000*P)) := mul_le_mul_of_nonneg_left hy (by positivity)
      _ = _ := by field_simp <;> ring
  have hY : ‖(5:ℂ)*y^2‖ ≤ 5/(1000000*P^2) := by
    calc
      _ = 5*‖y‖^2 := by simp [norm_mul,norm_pow]
      _ ≤ 5*(1/(1000*P))^2 := mul_le_mul_of_nonneg_left hy2 (by norm_num)
      _ = _ := by field_simp; ring
  let v : ℂ := 5*x^2+6*x*y+5*y^2
  have hVupper : ‖v‖ ≤ 5006005/(1000000*P^2) := by
    have h1 := norm_add_le ((5:ℂ)*x^2+6*x*y) ((5:ℂ)*y^2)
    have h2 := norm_add_le ((5:ℂ)*x^2) ((6:ℂ)*x*y)
    rw [hX] at h2
    have heq : 5/P^2+6/(1000*P^2)+5/(1000000*P^2) =
        5006005/(1000000*P^2) := by field_simp; ring
    change ‖v‖ ≤ _+_ at h1
    linarith only [h1,h2,hXY,hY,heq]
  have hVlower : 4993995/(1000000*P^2) ≤ ‖v‖ := by
    have h1 := norm_sub_le v ((6:ℂ)*x*y+(5:ℂ)*y^2)
    have heqV : v-((6:ℂ)*x*y+(5:ℂ)*y^2) = (5:ℂ)*x^2 := by dsimp [v]; ring
    rw [heqV,hX] at h1
    have h2 := norm_add_le ((6:ℂ)*x*y) ((5:ℂ)*y^2)
    have heq : 5/P^2-6/(1000*P^2)-5/(1000000*P^2) =
        4993995/(1000000*P^2) := by field_simp; ring
    linarith only [h1,h2,hXY,hY,heq]
  have hc : ‖halfBinomialWeightedCoeff x y 4‖ = ‖x-y‖^2*‖v‖/128 := by
    rw [halfBinomialWeightedCoeff_four,norm_div,norm_mul,norm_neg,norm_pow]
    change ‖x-y‖^2*‖v‖/‖(128:ℂ)‖ = ‖x-y‖^2*‖v‖/128
    norm_num
  rw [hc]
  constructor
  · calc
      _ = (999/(1000*P))^2*(4993995/(1000000*P^2))/128 := by
        dsimp [coherentFourLeadingLower]
        field_simp
        ring
      _ ≤ ‖x-y‖^2*‖v‖/128 := div_le_div_of_nonneg_right
        (mul_le_mul hDlower2 hVlower (by positivity) (by positivity)) (by norm_num)
  · calc
      _ ≤ (1001/(1000*P))^2*(5006005/(1000000*P^2))/128 := div_le_div_of_nonneg_right
        (mul_le_mul hDupper2 hVupper (norm_nonneg _) (by positivity)) (by norm_num)
      _ = _ := by
        dsimp [coherentFourLeadingUpper]
        field_simp
        ring





end D1Bound5
end

