-- Prove2me | solution 1 for BookProof.QuadraticRotation.pderiv_rotPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:08:40.594471+00:00
-- url     : https://prove2.me/submissions/e7376e86-517c-494f-9345-6664936370b4

-- Generated from ChapterQuadraticRotationEsa.lean — solution of BookProof.QuadraticRotation.pderiv_rotPoly
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Theorems.Thm_BookProof_QuadraticRotation_rotPoly_X
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
theorem solution (O : Matrix (Fin d) (Fin d) ℝ) (k : Fin d)
    (p : MvPolynomial (Fin d) ℂ) :
    pderiv k (rotPoly O p) = ∑ i, C ((O k i : ℝ) : ℂ) * rotPoly O (pderiv i p) := by

  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, Finset.sum_add_distrib, mul_add]
  | mul_X p i hp =>
      have hd : pderiv k (rotPoly O (X i)) = C ((O k i : ℝ) : ℂ) := by
        rw [rotPoly_X, map_sum]
        simp [Pi.single_apply]
      have hr : ∀ m : Fin d, pderiv m (p * X i)
          = pderiv m p * X i + (if m = i then p else 0) := by
        intro m
        rw [Derivation.leibniz, pderiv_X]
        by_cases h : m = i <;> simp [h, Pi.single_apply, smul_eq_mul, mul_comm, add_comm]
      have hRHS : ∑ m, C ((O k m : ℝ) : ℂ) * rotPoly O (pderiv m (p * X i))
          = (∑ m, C ((O k m : ℝ) : ℂ) * rotPoly O (pderiv m p)) * rotPoly O (X i)
            + C ((O k i : ℝ) : ℂ) * rotPoly O p := by
        have hsplit : ∀ m : Fin d, C ((O k m : ℝ) : ℂ) * rotPoly O (pderiv m (p * X i))
            = C ((O k m : ℝ) : ℂ) * rotPoly O (pderiv m p) * rotPoly O (X i)
              + (if m = i then C ((O k m : ℝ) : ℂ) * rotPoly O p else 0) := by
          intro m
          rw [hr m, map_add, map_mul, mul_add]
          by_cases h : m = i <;> simp [h, mul_assoc]
        rw [Finset.sum_congr rfl fun m _ => hsplit m, Finset.sum_add_distrib, Finset.sum_mul]
        congr 1
        simp
      rw [map_mul, Derivation.leibniz, hd, hp, hRHS]
      simp only [smul_eq_mul]
      ring
