-- Prove2me | solution 1 for BookProof.ChapterCoherentDynamics.inner_phaseRotate
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:07:02.151519+00:00
-- url     : https://prove2.me/submissions/0a9ea6f8-9d14-4aaa-8254-8cf017e8d0bd

-- Generated from ChapterCoherentDynamics.lean — solution of BookProof.ChapterCoherentDynamics.inner_phaseRotate
import Mathlib
import Definitions.Def_ChapterCoherentDynamics
open BookProof.ChapterCoherentDynamics



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterCoherentFidelity

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (theta : ℝ) (q k : EuclideanSpace ℂ (Fin n)) :
    (inner ℂ (phaseRotate theta q) (phaseRotate theta k) : ℂ) = inner ℂ q k := by

  rw [phaseRotate, phaseRotate, inner_smul_left, inner_smul_right, ← mul_assoc]
  have h : (starRingEnd ℂ) (Complex.exp (theta * Complex.I)) * Complex.exp (theta * Complex.I)
      = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self]
    norm_cast
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]
  rw [h, one_mul]
