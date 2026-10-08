-- Prove2me | solution 1 for BookProof.BookBrstYangMills.bosOpN_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:44:51.005691+00:00
-- url     : https://prove2.me/submissions/a69c5f69-6569-4231-acb7-255215feb747

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.bosOpN_zero
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution : bosOpN (0 : Module.End ℂ (FieldPoly N)) = 0 := by
 simp [bosOpN]
