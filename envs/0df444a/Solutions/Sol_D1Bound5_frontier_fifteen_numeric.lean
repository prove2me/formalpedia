-- Prove2me | solution 1 for D1Bound5.frontier_fifteen_numeric
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:30:27.635809+00:00
-- url     : https://prove2.me/submissions/1157db51-7c2a-4a54-8c70-ff98be16766a

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped Matrix.Norms.L2Operator BigOperators
open Matrix

namespace D1Bound5

theorem _root_.solution (A B C D : ℝ)
    (hA1 : 1 ≤ A) (hA3 : A < 3) (hB : 3 ≤ B) (hC : 15 ≤ C)
    (hD : 2*B*C < D)
    (hupper : A*B*C*D ≤
      (252/1000 : ℝ)*A^2+(256/1000)*B^2+(277/1000)*C^2+(282/1000)*D^2+
      (284/1000)*A*B+(284/1000)*A*C+(288/1000)*A*D+
      (286/1000)*B*C+(296/1000)*B*D+(362/1000)*C*D+1) :
    (59/20 : ℝ)*A*B*C < D := by
  have hA0 : 0 < A := by linarith only [hA1]
  have hB0 : 0 < B := by linarith only [hB]
  have hC0 : 0 < C := by linarith only [hC]
  have hBC : 45 ≤ B*C := by
    calc 45 = (3 : ℝ)*15 := by norm_num
         _ ≤ B*C := by gcongr
  have hD90 : 90 ≤ D := by linarith only [hD,hBC]
  have hD0 : 0 < D := by linarith only [hD90]
  let P := A*B*C*D
  have hP : 0 < P := by dsimp [P]; positivity
  have hbase : 4050 ≤ P := by
    calc 4050 = (1 : ℝ)*3*15*90 := by norm_num
         _ ≤ P := by dsimp [P]; gcongr
  have hcomp (X Y m : ℝ) (hX : 0 ≤ X) (hm : 0 < m) (hY : m ≤ Y)
      (hXY : P = X*Y) : X ≤ P/m := by
    apply (le_div_iff₀ hm).mpr
    rw [hXY]
    nlinarith only [mul_nonneg hX (sub_nonneg.mpr hY)]
  have hAB : A*B ≤ P/1350 := hcomp (A*B) (C*D) 1350 (by positivity) (by norm_num)
    (by
      calc
        1350 = (15 : ℝ)*90 := by norm_num
        _ ≤ C*D := by gcongr)
    (by dsimp [P]; ring)
  have hAC : A*C ≤ P/270 := hcomp (A*C) (B*D) 270 (by positivity) (by norm_num)
    (by
      calc
        270 = (3 : ℝ)*90 := by norm_num
        _ ≤ B*D := by gcongr)
    (by dsimp [P]; ring)
  have hAD : A*D ≤ P/45 := hcomp (A*D) (B*C) 45 (by positivity) (by norm_num) hBC
    (by dsimp [P]; ring)
  have hBC' : B*C ≤ P/90 := hcomp (B*C) (A*D) 90 (by positivity) (by norm_num)
    (by
      calc
        90 = (1 : ℝ)*90 := by norm_num
        _ ≤ A*D := by gcongr)
    (by dsimp [P]; ring)
  have hBD : B*D ≤ P/15 := hcomp (B*D) (A*C) 15 (by positivity) (by norm_num)
    (by
      calc
        15 = (1 : ℝ)*15 := by norm_num
        _ ≤ A*C := by gcongr)
    (by dsimp [P]; ring)
  have hCD : C*D ≤ P/3 := hcomp (C*D) (A*B) 3 (by positivity) (by norm_num)
    (by
      calc
        3 = (1 : ℝ)*3 := by norm_num
        _ ≤ A*B := by gcongr)
    (by dsimp [P]; ring)
  have hAsmall : A ≤ P/4050 := hcomp A (B*C*D) 4050 hA0.le (by norm_num)
    (by
      calc
        4050 = (3 : ℝ)*15*90 := by norm_num
        _ ≤ B*C*D := by gcongr)
    (by dsimp [P]; ring)
  have hA2 : A^2 ≤ P/1350 := by
    have hh := mul_nonneg hA0.le (sub_nonneg.mpr hA3.le)
    nlinarith only [hh,hAsmall]
  have hscaled := mul_le_mul_of_nonneg_left hD.le
    (show 0 ≤ A*B*C by positivity)
  have hAC2 : 225 ≤ A*C^2 := by
    calc 225 = (1 : ℝ)*15^2 := by norm_num
         _ ≤ A*C^2 := by gcongr
  have hAB2 : 9 ≤ A*B^2 := by
    calc 9 = (1 : ℝ)*3^2 := by norm_num
         _ ≤ A*B^2 := by gcongr
  have hB2 : B^2 ≤ P/450 := by
    have hh := mul_nonneg (sub_nonneg.mpr hAC2) (sq_nonneg B)
    dsimp [P]
    nlinarith only [hh,hscaled]
  have hC2 : C^2 ≤ P/18 := by
    have hh := mul_nonneg (sub_nonneg.mpr hAB2) (sq_nonneg C)
    dsimp [P]
    nlinarith only [hh,hscaled]
  by_contra hbad
  have hD2 : D^2 ≤ (59/20 : ℝ)*P := by
    have hh := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hbad)) hD0.le
    dsimp [P]
    nlinarith only [hh]
  change P ≤ _ at hupper
  nlinarith only [hupper,hA2,hB2,hC2,hD2,hAB,hAC,hAD,hBC',hBD,hCD,hbase,hP]





end D1Bound5
end
