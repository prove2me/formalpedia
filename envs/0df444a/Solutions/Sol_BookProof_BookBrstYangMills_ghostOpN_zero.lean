-- Prove2me | solution 1 for BookProof.BookBrstYangMills.ghostOpN_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:45:21.671884+00:00
-- url     : https://prove2.me/submissions/0b100856-e5f5-49b3-b034-586aa67a967b

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.ghostOpN_zero
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution : ghostOpN (0 : Module.End ℂ (GhostSpace N)) = 0 := by
 simp [ghostOpN]
