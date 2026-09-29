-- Prove2me | solution 1 for BookProof.YangMillsFieldStrength.fieldStrengthMul_eq_Fbook
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:27:15.619838+00:00
-- url     : https://prove2.me/submissions/f9cd2a6f-89e8-4433-a43d-be382722f123

-- Generated from ChapterYangMillsFieldStrength.lean — solution of BookProof.YangMillsFieldStrength.fieldStrengthMul_eq_Fbook
import Mathlib
import Definitions.Def_ChapterYangMillsFieldStrength
open BookProof.YangMillsFieldStrength














open Complex



variable {R : Type*} [Ring R]









variable {R : Type*} [Ring R] [Algebra ℂ R]

set_option maxHeartbeats 1000000 in
theorem solution
    (δ : Fin 3 → R → R) (g : ℝ) (A : Fin 3 → R)
    (hsmul : ∀ (j : Fin 3) (c : ℂ) x, δ j (c • x) = c • δ j x) (j k : Fin 3) :
    fieldStrengthMul δ (fun j => (-(I * (g : ℂ))) • A j) j k
      = (-(I * (g : ℂ))) • Fbook δ g A j k := by

  simp only [fieldStrengthMul, Fbook]
  rw [hsmul, hsmul, smul_mul_smul_comm, smul_mul_smul_comm]
  module
