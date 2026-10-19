-- Prove2me | solution 1 for BookProof.ChapterWeakValue.dslit_weakValue
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:45:53.419765+00:00
-- url     : https://prove2.me/submissions/d545d6db-e9ff-4bbf-9758-8235e9cb8bd0

-- Generated from ChapterWeakValue.lean — solution of BookProof.ChapterWeakValue.dslit_weakValue
import Mathlib
import Definitions.Def_ChapterWeakValue
import Theorems.Thm_BookProof_ChapterWeakValue_weakValue_proj
import Theorems.Thm_BookProof_ChapterWeakValue_hadamard_psi0
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterWeakValue



open scoped BigOperators Matrix
open BookProof.ChapterDoubleSlit


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution :
    weakValue (H *ᵥ psi0) psi0 (projMat 0) = 1 ∧
      weakValue (H *ᵥ psi0) psi0 (projMat 1) = 0 := by
  have hip : ip psi0 (H *ᵥ psi0) = (1 / Real.sqrt 2 : ℂ) := by
    rw [hadamard_psi0]; simp [ip, psi0, Fin.sum_univ_two]
  constructor
  · rw [weakValue_proj, hip, hadamard_psi0]
    simp [psi0]
  · rw [weakValue_proj, hip, hadamard_psi0]
    simp [psi0]
