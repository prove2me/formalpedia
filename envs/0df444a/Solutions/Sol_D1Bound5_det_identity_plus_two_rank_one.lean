-- Prove2me | solution 1 for D1Bound5.det_identity_plus_two_rank_one
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:53:59.943057+00:00
-- url     : https://prove2.me/submissions/70420681-50e4-424b-b86a-f9f5171d8424

import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open scoped NumberField BigOperators
open Matrix Module

namespace D1Bound5

/-- Rank-two determinant formula over any commutative ring, including
rings with zero divisors. No inverse of I+J is required. -/
theorem _root_.solution {R n : Type*} [CommRing R]
    [Fintype n] [DecidableEq n] (v : n → R) :
    Matrix.det (fun i j => (if i=j then 1 else 0)+1+v i*v j) =
      (1+(Fintype.card n : R))*(1+∑ i, v i^2)-(∑ i, v i)^2 := by
  let A : Matrix n (Fin 2) R := fun i j => if j=0 then 1 else v i
  have haa (i j : n) : (A*A.transpose) i j = 1+v i*v j := by
    change (∑ k : Fin 2, A i k*A j k) = _
    simp [A,Fin.sum_univ_two]
  have h00 : (A.transpose*A) 0 0 = (Fintype.card n : R) := by
    change (∑ i : n, A i 0*A i 0) = _
    simp [A]
  have h01 : (A.transpose*A) 0 1 = ∑ i, v i := by
    change (∑ i : n, A i 0*A i 1) = _
    simp [A]
  have h10 : (A.transpose*A) 1 0 = ∑ i, v i := by
    change (∑ i : n, A i 1*A i 0) = _
    simp [A]
  have h11 : (A.transpose*A) 1 1 = ∑ i, v i^2 := by
    change (∑ i : n, A i 1*A i 1) = _
    simp [A,pow_two]
  calc
    _ = (1+A*A.transpose).det := by
      congr 1
      ext i j
      change (if i=j then 1 else 0)+1+v i*v j =
        (if i=j then 1 else 0)+(A*A.transpose) i j
      rw [haa]
      ring
    _ = (1+A.transpose*A).det := Matrix.det_one_add_mul_comm A A.transpose
    _ = _ := by
      rw [Matrix.det_fin_two]
      simp [Matrix.add_apply,Matrix.one_apply,h00,h01,h10,h11,pow_two]









end D1Bound5
end
