-- Prove2me | solution 1 for BookProof.BookBrstYangMills.bosOpN_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:44:38.557401+00:00
-- url     : https://prove2.me/submissions/d5e250f7-daab-4a6d-8e21-68559282a5c5

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.bosOpN_one
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution : bosOpN (1 : Module.End ℂ (FieldPoly N)) = 1 := by

  simp [bosOpN, Module.End.one_eq_id, LinearMap.rTensor_id]
