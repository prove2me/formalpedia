-- Prove2me | solution 1 for ForecastAggLearn.hstar_aggregates
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-10T12:16:23.911805+00:00
-- url     : https://prove2.me/submissions/531f81e4-d5d7-4ec6-b54d-7baae8c269e1

import Definitions.Def_ForecastAggLearn_hstar
import Mathlib.LinearAlgebra.Matrix.DotProduct

open ForecastAggLearn

theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (hA : Function.Injective A.mulVec) :
    IsUnit (A.transpose * A).det ∧ ∀ y : Fin m → ℝ, hstar A ⬝ᵥ A.mulVec y = ∑ j, y j := by
  have hG : Function.Injective (A.transpose * A).mulVec := by
    intro x y hxy
    have hz : (A.transpose * A).mulVec (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have hs := Matrix.dotProduct_transpose_mulVec A (x - y) (A.mulVec (x - y))
    rw [Matrix.mulVec_mulVec, hz, dotProduct_zero] at hs
    have hAz : A.mulVec (x - y) = 0 := dotProduct_self_eq_zero.mp hs.symm
    apply sub_eq_zero.mp
    apply hA
    simpa only [Matrix.mulVec_zero] using hAz
  have hdet : IsUnit (A.transpose * A).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hG)
  refine ⟨hdet, fun y => ?_⟩
  unfold hstar
  rw [← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  simp [dotProduct]

#print axioms solution
