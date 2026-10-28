-- Prove2me | solution 1 for D1Bound5.coherent_retained_h48_size_parameters
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:25:01.659997+00:00
-- url     : https://prove2.me/submissions/45a76175-f57b-4911-8cf2-4c457ef17f2e

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

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5

/-- The no-small-entry retained configuration supplies every analytic
size condition, and the strong gap on the last two anchors excludes
the three-anchor zero window. -/
theorem _root_.solution
    (A B S T C : ℝ) (hA : 3 ≤ A) (hAB : A ≤ B) (hBS : B ≤ S)
    (hT : 2*A*B*S < T) (hC : 3*A*B*S*T < C) :
    5*S ≤ T ∧ 5*B*S*T ≤ C ∧ 48 ≤ A*T ∧ 4*T ≤ C ∧ 10000 < T*C ∧
      (B^2*T^3 < (10001/10000 : ℝ)*C → 15*A*B*S*T^2 < C) := by
  have hA0 : 0 < A := by linarith
  have hB3 : 3 ≤ B := hA.trans hAB
  have hS3 : 3 ≤ S := hB3.trans hBS
  have hB0 : 0 < B := by linarith
  have hS0 : 0 < S := by linarith
  have hAB9 : 9 ≤ A*B := by
    have h := mul_le_mul hA hB3 (by norm_num : (0:ℝ)≤3) hA0.le
    nlinarith only [h]
  have hABS27 : 27 ≤ A*B*S := by
    have h := mul_le_mul hAB9 hS3 (by norm_num : (0:ℝ)≤3) (by positivity : 0≤A*B)
    nlinarith only [h]
  have hT54 : 54 < T := by nlinarith only [hT,hABS27]
  have hT0 : 0 < T := by linarith
  have hC81 : 81*T < C := by
    have h := mul_le_mul_of_nonneg_right hABS27 (by positivity : 0≤3*T)
    nlinarith only [h,hC]
  have hT5S : 5*S ≤ T := by
    have h := mul_le_mul_of_nonneg_right hAB9 (by positivity : 0≤2*S)
    nlinarith only [h,hT,hS0]
  have hC5 : 5*B*S*T ≤ C := by
    have h := mul_le_mul_of_nonneg_right hA (by positivity : 0≤3*B*S*T)
    nlinarith only [h,hC,mul_pos (mul_pos hB0 hS0) hT0]
  have hAT : 48 ≤ A*T := by
    have h := mul_le_mul_of_nonneg_right hA hT0.le
    nlinarith only [h,hT54]
  have hTC : 10000 < T*C := by
    have h := mul_lt_mul_of_pos_left hC81 hT0
    have ht2 : 54^2 < T^2 := by nlinarith only [hT54,sq_nonneg (T-54)]
    nlinarith only [h,ht2]
  refine ⟨hT5S,hC5,hAT,by linarith,hTC,?_⟩
  intro hgap
  have hBsq : 9 ≤ B^2 := by nlinarith only [hB3,sq_nonneg (B-3)]
  have h1 := mul_lt_mul_of_pos_right hT (by positivity : 0<B^2*T^2)
  have h2 := mul_le_mul_of_nonneg_right hBsq (by positivity : 0≤2*A*B*S*T^2)
  have hprod : 0 < A*B*S*T^2 := by positivity
  nlinarith only [h1,h2,hgap,hprod]



end D1Bound5
end
