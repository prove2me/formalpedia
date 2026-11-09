-- Prove2me | solution 1 for BookProof.QuadraticRotation.rotPoly_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:14:00.893254+00:00
-- url     : https://prove2.me/submissions/ae7a858b-2b2f-4b09-bc9e-008b720e0db1

-- Generated from ChapterQuadraticRotationEsa.lean — solution of BookProof.QuadraticRotation.rotPoly_pderiv
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Theorems.Thm_BookProof_QuadraticRotation_pderiv_rotPoly
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
theorem solution {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (i : Fin d)
    (p : MvPolynomial (Fin d) ℂ) :
    rotPoly O (pderiv i p) = ∑ k, ((O k i : ℝ) : ℂ) • pderiv k (rotPoly O p) := by

  have hexp : ∀ k : Fin d, ((O k i : ℝ) : ℂ) • pderiv k (rotPoly O p)
      = ∑ m, ((O k i * O k m : ℝ) : ℂ) • rotPoly O (pderiv m p) := by
    intro k
    rw [pderiv_rotPoly, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl fun k _ => hexp k, Finset.sum_comm]
  have hm : ∀ m : Fin d, ∑ k, ((O k i * O k m : ℝ) : ℂ) • rotPoly O (pderiv m p)
      = (if i = m then (1 : ℂ) else 0) • rotPoly O (pderiv m p) := by
    intro m
    rw [← Finset.sum_smul]
    congr 1
    have h1 := congrFun (congrFun hO i) m
    have h2 : ∑ k, O k i * O k m = if i = m then (1 : ℝ) else 0 := by
      simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply] using h1
    rw [show (∑ k, ((O k i * O k m : ℝ) : ℂ)) = ((∑ k, O k i * O k m : ℝ) : ℂ) by
        push_cast; ring, h2]
    by_cases h : i = m <;> simp [h]
  rw [Finset.sum_congr rfl fun m _ => hm m]
  simp
