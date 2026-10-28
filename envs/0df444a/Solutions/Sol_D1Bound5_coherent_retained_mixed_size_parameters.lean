-- Prove2me | solution 1 for D1Bound5.coherent_retained_mixed_size_parameters
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:06:44.068736+00:00
-- url     : https://prove2.me/submissions/e2d8c965-0986-45e4-badb-c2f81a892099

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
namespace D1Bound5

/-- The preliminary retained size bounds when only the first anchor may
have modulus below three. The first L2 gap is needed to obtain the
input for the second L2 gap. -/
theorem _root_.solution
    (A B S T C : ℝ) (hA : 1 ≤ A) (hB : 3 ≤ B) (hBS : B ≤ S)
    (hAT32 : 32 ≤ A*T) (hT : 2*A*B*S < T) (hC : 3*A*B*S*T < C) :
    5*S ≤ T ∧ 5*A*B*T ≤ C ∧ 32 ≤ A*T ∧ 4*T ≤ C ∧ 10000 < T*C ∧
      (A^2*T^3 < (10001/10000 : ℝ)*C → 5*B*S*T ≤ C) ∧
      (B^2*T^3 < (10001/10000 : ℝ)*C → (179/10 : ℝ)*A*B*S*T^2 < C) := by
  have hA0 : 0 < A := by linarith only [hA]
  have hB0 : 0 < B := by linarith only [hB]
  have hS3 : 3 ≤ S := hB.trans hBS
  have hS0 : 0 < S := by linarith only [hS3]
  have hT0 : 0 < T := lt_trans (by positivity : 0 < 2*A*B*S) hT
  have hAB3 : 3 ≤ A*B := by
    have hh := mul_le_mul hA hB (by norm_num : (0 : ℝ) ≤ 3) hA0.le
    nlinarith only [hh]
  have hABS9 : 9 ≤ A*B*S := by
    have hh := mul_le_mul hAB3 hS3 (by norm_num : (0 : ℝ) ≤ 3) (by positivity : 0 ≤ A*B)
    nlinarith only [hh]
  have hC27 : 27*T < C := by
    have hh := mul_le_mul_of_nonneg_right hABS9 (by positivity : 0 ≤ 3*T)
    nlinarith only [hh,hC]
  have hT5S : 5*S ≤ T := by
    have hh := mul_le_mul_of_nonneg_right hAB3 (by positivity : 0 ≤ 2*S)
    nlinarith only [hh,hT,hS0]
  have hC5 : 5*A*B*T ≤ C := by
    have hh := mul_le_mul_of_nonneg_right hS3 (by positivity : 0 ≤ 3*A*B*T)
    nlinarith only [hh,hC,mul_pos (mul_pos hA0 hB0) hT0]
  have hTC : 10000 < T*C := by
    have hBS9 : 9 ≤ B*S := by
      have hh := mul_le_mul hB hS3 (by norm_num : (0 : ℝ) ≤ 3) hB0.le
      nlinarith only [hh]
    have hh := mul_le_mul_of_nonneg_right hBS9 (by positivity : 0 ≤ 3*A*T)
    have hC864 : 864 < C := by nlinarith only [hh,hC,hAT32]
    have hT18 : 18 < T := by nlinarith only [hT,hABS9]
    have hp := mul_lt_mul hT18 hC864.le (by norm_num : (0 : ℝ) < 864) hT0.le
    norm_num at hp
    linarith only [hp]
  refine ⟨hT5S,hC5,hAT32,by linarith only [hC27,hT0],hTC,?_,?_⟩
  · intro hgap
    have hBS9 : 9 ≤ B*S := by
      have hh := mul_le_mul hB hS3 (by norm_num : (0 : ℝ) ≤ 3) hB0.le
      nlinarith only [hh]
    have h2 : 2*B*S < T := by
      have hh := mul_le_mul_of_nonneg_right hA (by positivity : 0 ≤ 2*B*S)
      nlinarith only [hh,hT]
    have hT2 : 4*B^2*S^2 < T^2 := by
      have hh := mul_pos (sub_pos.mpr h2) (show 0 < T+2*B*S by positivity)
      nlinarith only [hh]
    have hBSsq : 36*B*S ≤ 4*B^2*S^2 := by
      have hh := mul_le_mul_of_nonneg_right hBS9 (by positivity : 0 ≤ 4*B*S)
      nlinarith only [hh]
    have hA2 : (1 : ℝ) ≤ A^2 := by nlinarith only [hA,sq_nonneg (A-1)]
    have hAT2 := mul_le_mul_of_nonneg_right hA2 (sq_nonneg T)
    have hratio : 5*(10001/10000 : ℝ)*B*S < A^2*T^2 := by
      have hpos : 0 < B*S := by positivity
      nlinarith only [hT2,hBSsq,hAT2,hpos]
    have hh := mul_lt_mul_of_pos_right hratio hT0
    nlinarith only [hh,hgap]
  · intro hgap
    have hBsq : 9 ≤ B^2 := by nlinarith only [hB,sq_nonneg (B-3)]
    have h1 := mul_lt_mul_of_pos_right hT (by positivity : 0 < B^2*T^2)
    have h2 := mul_le_mul_of_nonneg_right hBsq (by positivity : 0 ≤ 2*A*B*S*T^2)
    have hprod : 0 < A*B*S*T^2 := by positivity
    nlinarith only [h1,h2,hgap,hprod]

end D1Bound5
end
