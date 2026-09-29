-- Prove2me | solution 1 for BookProof.NavierStokesFlow.nsHamiltonian_ne_zero_example
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:38:05.310226+00:00
-- url     : https://prove2.me/submissions/b8f6a0e8-aab7-492b-983e-0aeaf4617c95

-- Generated from ChapterNavierStokesFlow.lean — solution of BookProof.NavierStokesFlow.nsHamiltonian_ne_zero_example
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow



open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

set_option maxHeartbeats 1000000 in
theorem solution :
    nsHamiltonian (nsTruncationOfDiagonal (n := 1) (fun _ _ => 1) (fun _ => 1)
      (fun _ => Matrix.conjTranspose_one) 0) ≠ 0 := by

  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [nsHamiltonian, nsAdvection, nsVelocity, nsGradVelocity, nsLapVelocity,
    nsTruncationOfDiagonal, Matrix.ofNat_apply] at h00
