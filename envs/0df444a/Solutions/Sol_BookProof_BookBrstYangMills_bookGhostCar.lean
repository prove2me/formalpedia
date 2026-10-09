-- Prove2me | solution 1 for BookProof.BookBrstYangMills.bookGhostCar
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:29:14.768069+00:00
-- url     : https://prove2.me/submissions/8f54ffd6-aa0e-4e87-8ec2-baca2f6b51c6

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.bookGhostCar
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
import Theorems.Thm_BookProof_BookBrstYangMills_ghostN_car
import Theorems.Thm_BookProof_BookBrstYangMills_ghostOpN_mul
import Theorems.Thm_BookProof_BookBrstYangMills_ghostOpN_add
import Theorems.Thm_BookProof_BookBrstYangMills_ghostOpN_one
import Theorems.Thm_BookProof_BookBrstYangMills_ghostOpN_zero
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution : GhostCAR (chiOp (N := N)) (betaOp (N := N)) := by

  classical
  constructor
  · intro a b
    rw [chiOp, chiOp, ← ghostOpN_mul, ← ghostOpN_mul, ← ghostOpN_add,
      (ghostN_car (N := N)).chichi a b, ghostOpN_zero]
  · intro a b
    rw [betaOp, betaOp, ← ghostOpN_mul, ← ghostOpN_mul, ← ghostOpN_add,
      (ghostN_car (N := N)).betabeta a b, ghostOpN_zero]
  · intro a b
    rw [betaOp, chiOp, ← ghostOpN_mul, ← ghostOpN_mul, ← ghostOpN_add,
      (ghostN_car (N := N)).betachi a b]
    by_cases h : a = b
    · simp [h, ghostOpN_one]
    · simp [h, ghostOpN_zero]
