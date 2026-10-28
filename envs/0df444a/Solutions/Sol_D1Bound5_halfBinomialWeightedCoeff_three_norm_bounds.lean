-- Prove2me | solution 1 for D1Bound5.halfBinomialWeightedCoeff_three_norm_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:37:53.246395+00:00
-- url     : https://prove2.me/submissions/68499577-eb8e-4938-bd85-22cfb5c8fec4

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





/-- Frozen v4 equation (integrated-5), degree three. -/
theorem halfBinomialWeightedCoeff_three (x y : ℂ) :
    halfBinomialWeightedCoeff x y 3 = (x^2 - y^2) * (x-y) / 16 := by
  norm_num [halfBinomialWeightedCoeff, Finset.antidiagonal,
    halfCoeff_zero, halfCoeff_one, halfCoeff_two, halfCoeff_three]
  ring



end D1Bound5
end

section
open Finset

noncomputable section

namespace D1Bound5









/-- Both sharp elementary degree-three bounds under quarter-size
terminal separation.  The lower bound is a reverse triangle estimate
on each of the two factors, so no phase or square-root sign is assumed. -/
theorem _root_.solution
    (x y : ℂ) (P : ℝ) (hP : 0 < P)
    (hx : ‖x‖ = 1/P) (hy : ‖y‖ ≤ 1/(4*P)) :
    45/(1024*P^3) ≤ ‖halfBinomialWeightedCoeff x y 3‖ ∧
    ‖halfBinomialWeightedCoeff x y 3‖ ≤ 85/(1024*P^3) := by
  have hy2 : ‖y‖^2 ≤ (1/(4*P))^2 := by gcongr
  have hUupper : ‖x-y‖ ≤ 5/(4*P) := by
    calc
      ‖x-y‖ ≤ ‖x‖+‖y‖ := norm_sub_le _ _
      _ ≤ 1/P+1/(4*P) := by rw [hx]; exact add_le_add le_rfl hy
      _ = _ := by field_simp; ring
  have hUlower : 3/(4*P) ≤ ‖x-y‖ := by
    have h := norm_add_le (x-y) y
    rw [sub_add_cancel, hx] at h
    have heq : 1/P-1/(4*P) = 3/(4*P) := by field_simp; ring
    linarith only [h, hy, heq]
  have hVupper : ‖x^2-y^2‖ ≤ 17/(16*P^2) := by
    calc
      ‖x^2-y^2‖ ≤ ‖x^2‖+‖y^2‖ := norm_sub_le _ _
      _ = (1/P)^2+‖y‖^2 := by rw [norm_pow, norm_pow, hx]
      _ ≤ (1/P)^2+(1/(4*P))^2 := add_le_add le_rfl hy2
      _ = _ := by field_simp; ring
  have hVlower : 15/(16*P^2) ≤ ‖x^2-y^2‖ := by
    have h : ‖(x^2-y^2)+y^2‖ ≤ ‖x^2-y^2‖+‖y^2‖ :=
      norm_add_le (x^2-y^2) (y^2)
    rw [sub_add_cancel, Complex.norm_pow, Complex.norm_pow, hx] at h
    have heq : (1/P)^2-(1/(4*P))^2 = 15/(16*P^2) := by field_simp; ring
    linarith only [h, hy2, heq]
  have hcoeff : ‖halfBinomialWeightedCoeff x y 3‖ = ‖x^2-y^2‖*‖x-y‖/16 := by
    rw [halfBinomialWeightedCoeff_three, norm_div, norm_mul]
    norm_num
  rw [hcoeff]
  constructor
  · calc
      _ = (15/(16*P^2))*(3/(4*P))/16 := by field_simp; ring
      _ ≤ ‖x^2-y^2‖*‖x-y‖/16 :=
        div_le_div_of_nonneg_right
          (mul_le_mul hVlower hUlower (by positivity) (norm_nonneg _)) (by norm_num)
  · calc
      _ ≤ (17/(16*P^2))*(5/(4*P))/16 :=
        div_le_div_of_nonneg_right
          (mul_le_mul hVupper hUupper (norm_nonneg _) (by positivity)) (by norm_num)
      _ = _ := by field_simp; ring







end D1Bound5
end
