-- Prove2me | solution 1 for BookProof.BookBrstYangMills.bosOpN_sub
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:42:59.717156+00:00
-- url     : https://prove2.me/submissions/936a9b1f-dded-4f1c-95a7-59e9b2078bd3

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.bosOpN_sub
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution (S T : Module.End ℂ (FieldPoly N)) :
    bosOpN (S - T) = bosOpN S - bosOpN T := by
 simp [bosOpN]
