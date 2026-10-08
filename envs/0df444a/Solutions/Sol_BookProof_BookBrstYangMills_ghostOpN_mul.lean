-- Prove2me | solution 1 for BookProof.BookBrstYangMills.ghostOpN_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:45:05.923933+00:00
-- url     : https://prove2.me/submissions/ed370ead-307d-45b1-961b-4be8e5666a8c

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.ghostOpN_mul
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution (S T : Module.End ℂ (GhostSpace N)) :
    ghostOpN (S * T) = ghostOpN S * ghostOpN T := by

  simp [ghostOpN, Module.End.mul_eq_comp, LinearMap.lTensor_comp]
