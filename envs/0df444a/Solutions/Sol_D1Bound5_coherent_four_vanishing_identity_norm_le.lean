-- Prove2me | solution 1 for D1Bound5.coherent_four_vanishing_identity_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:09.098691+00:00
-- url     : https://prove2.me/submissions/8a5fe53e-a4de-48f8-ad25-22eecf70e717

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
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open Finset

namespace D1Bound5



/-- The rational identity forced by simultaneous vanishing gives the
manuscript's sharp enough upper bound for `|pq+1|`. -/
theorem _root_.solution
    (e2 e3 e4 p q : ℂ) (A B S T : ℝ)
    (hA : 1 ≤ A) (hAB : A ≤ B) (hBS : B ≤ S) (hST : S ≤ T)
    (he2 : ‖e2‖ ≤ 6*S*T) (he3 : ‖e3‖ ≤ 4*B*S*T)
    (he4 : ‖e4‖ = A*B*S*T)
    (hid : p*q+1 = (e2+1-e3^2/(4*e4))^2/(4*e4)) :
    ‖p*q+1‖ ≤ 121*B*S*T/(4*A^3) := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := hA0.trans_le hAB
  have hS0 : 0 < S := hB0.trans_le hBS
  have hT0 : 0 < T := hS0.trans_le hST
  have hS1 : 1 ≤ S := hA.trans (hAB.trans hBS)
  have hT1 : 1 ≤ T := hS1.trans hST
  have hST1 : 1 ≤ S*T := by
    have h := mul_le_mul hS1 hT1 (by norm_num : (0 : ℝ) ≤ 1) hS0.le
    simpa using h
  have hABST : A ≤ B*S*T := by
    have h := mul_le_mul_of_nonneg_left hST1 hB0.le
    nlinarith only [h, hAB]
  have hAST : A*S*T ≤ B*S*T := by
    have h := mul_le_mul_of_nonneg_right hAB (by positivity : 0 ≤ S*T)
    nlinarith only [h]
  have hden : ‖(4 : ℂ)*e4‖ = 4*(A*B*S*T) := by
    rw [norm_mul, he4]
    norm_num
  have hE3sq : ‖e3‖^2 ≤ (4*B*S*T)^2 := by gcongr
  have hterm : ‖e3^2/((4 : ℂ)*e4)‖ ≤ 4*B*S*T/A := by
    rw [norm_div, norm_pow, hden]
    calc
      ‖e3‖^2 / (4*(A*B*S*T)) ≤ (4*B*S*T)^2 / (4*(A*B*S*T)) :=
        div_le_div_of_nonneg_right hE3sq (by positivity)
      _ = _ := by field_simp <;> ring
  have hinner : ‖e2+1-e3^2/(4*e4)‖ ≤ 6*S*T+1+4*B*S*T/A := by
    have h := norm_sub_le (e2+1) (e3^2/(4*e4))
    have h' := norm_add_le e2 (1 : ℂ)
    rw [norm_one] at h'
    linarith only [h, h', he2, hterm]
  have hcoarse : 6*S*T+1+4*B*S*T/A ≤ 11*B*S*T/A := by
    apply (mul_le_mul_iff_of_pos_right hA0).mp
    have heq1 : (6*S*T+1+4*B*S*T/A)*A = 6*A*S*T+A+4*B*S*T := by field_simp <;> ring
    have heq2 : (11*B*S*T/A)*A = 11*B*S*T := by field_simp <;> ring
    rw [heq1, heq2]
    nlinarith only [hABST, hAST]
  have hinner2 : ‖e2+1-e3^2/(4*e4)‖^2 ≤ (11*B*S*T/A)^2 := by
    have h := hinner.trans hcoarse
    gcongr
  rw [hid, norm_div, norm_pow, hden]
  calc
    _ ≤ (11*B*S*T/A)^2 / (4*(A*B*S*T)) :=
      div_le_div_of_nonneg_right hinner2 (by positivity)
    _ = _ := by field_simp; ring











end D1Bound5
end
