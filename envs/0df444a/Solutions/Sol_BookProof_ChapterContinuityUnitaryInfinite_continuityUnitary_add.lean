-- Prove2me | solution 1 for BookProof.ChapterContinuityUnitaryInfinite.continuityUnitary_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:06:04.867979+00:00
-- url     : https://prove2.me/submissions/537e0c66-7fc9-4570-b26d-5ff1739373d4

-- Generated from ChapterContinuityUnitaryInfinite.lean — solution of BookProof.ChapterContinuityUnitaryInfinite.continuityUnitary_add
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite








open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem solution (v : LinfZ) (s t : ℝ) :
    continuityUnitary v (s + t) = continuityUnitary v s * continuityUnitary v t := by

  let +nondep : NormedAlgebra ℚ (L2Z →L[ℂ] L2Z) := .restrictScalars ℚ ℂ _
  have hcomm : Commute (((s : ℂ) * Complex.I) • continuityHamiltonian v)
      (((t : ℂ) * Complex.I) • continuityHamiltonian v) := by
    simp [Commute, SemiconjBy, smul_smul, mul_comm]
  have hsum : (((s + t : ℝ) : ℂ) * Complex.I) • continuityHamiltonian v
      = ((s : ℂ) * Complex.I) • continuityHamiltonian v
        + ((t : ℂ) * Complex.I) • continuityHamiltonian v := by
    rw [← add_smul]
    push_cast
    ring_nf
  rw [continuityUnitary, hsum, NormedSpace.exp_add_of_commute hcomm]
  rfl
