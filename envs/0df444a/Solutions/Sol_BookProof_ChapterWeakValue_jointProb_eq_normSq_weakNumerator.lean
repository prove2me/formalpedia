-- Prove2me | solution 1 for BookProof.ChapterWeakValue.jointProb_eq_normSq_weakNumerator
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:21:32.121742+00:00
-- url     : https://prove2.me/submissions/5bff748c-71bd-47fd-8f0d-cf120400e880

-- Generated from ChapterWeakValue.lean — solution of BookProof.ChapterWeakValue.jointProb_eq_normSq_weakNumerator
import Mathlib
import Definitions.Def_ChapterWeakValue
import Theorems.Thm_BookProof_ChapterWeakValue_ip_projMat
import Definitions.Def_ChapterTrajectory
open BookProof.ChapterWeakValue



open scoped BigOperators Matrix


variable {n : ℕ}
open BookProof.ChapterTrajectory

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (U V : Matrix (Fin n) (Fin n) ℂ)
    (psi : Fin n → ℂ) (f a : Fin n) :
    ‖ip (postSelect V f) (projMat a *ᵥ (U *ᵥ psi))‖ ^ 2 = jointProb U V psi f a := by

  rw [ip_projMat, jointProb, midProb, transProb]
  simp [postSelect, mul_pow]
  ring
