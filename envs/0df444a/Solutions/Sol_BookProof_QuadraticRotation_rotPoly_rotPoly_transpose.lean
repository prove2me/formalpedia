-- Prove2me | solution 1 for BookProof.QuadraticRotation.rotPoly_rotPoly_transpose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:08:44.691458+00:00
-- url     : https://prove2.me/submissions/88b61fdb-c407-4fd2-aafa-7a8d7605e87d

-- Generated from ChapterQuadraticRotationEsa.lean — solution of BookProof.QuadraticRotation.rotPoly_rotPoly_transpose
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Theorems.Thm_BookProof_QuadraticRotation_rotPoly_X
import Theorems.Thm_BookProof_QuadraticRotation_rotPoly_C
open BookProof.QuadraticRotation




open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (p : MvPolynomial (Fin d) ℂ) : rotPoly O (rotPoly Oᵀ p) = p := by

  have hOO : O * Oᵀ = 1 := mul_eq_one_comm.mp hO
  have hgen : ∀ i : Fin d, rotPoly O (rotPoly Oᵀ (X i)) = X i := by
    intro i
    rw [rotPoly_X, map_sum]
    have hstep : ∀ j : Fin d, rotPoly O (C ((Oᵀ j i : ℝ) : ℂ) * X j)
        = ∑ k, C (((O i j * O k j : ℝ)) : ℂ) * X k := by
      intro j
      rw [map_mul, rotPoly_C, rotPoly_X, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_assoc, ← map_mul]
      norm_num [Matrix.transpose_apply]
    rw [Finset.sum_congr rfl fun j _ => hstep j, Finset.sum_comm]
    have hk : ∀ k : Fin d, ∑ j, C (((O i j * O k j : ℝ)) : ℂ) * X k
        = (if i = k then (1 : MvPolynomial (Fin d) ℂ) else 0) * X k := by
      intro k
      rw [← Finset.sum_mul]
      congr 1
      have h1 := congrFun (congrFun hOO i) k
      have h2 : ∑ j, O i j * O k j = if i = k then (1 : ℝ) else 0 := by
        simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply] using h1
      rw [← map_sum,
        show (∑ j, ((O i j * O k j : ℝ) : ℂ)) = ((∑ j, O i j * O k j : ℝ) : ℂ) by
          push_cast; ring,
        h2]
      by_cases h : i = k <;> simp [h]
    rw [Finset.sum_congr rfl fun k _ => hk k]
    simp
  have hcomp := MvPolynomial.algHom_ext (f := (rotPoly O).comp (rotPoly Oᵀ))
    (g := AlgHom.id ℂ (MvPolynomial (Fin d) ℂ)) (by intro i; simpa using hgen i)
  exact congrArg (fun f => f p) hcomp
