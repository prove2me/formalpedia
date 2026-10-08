-- Prove2me | solution 1 for BookProof.BookBrstYangMills.ghostOpN_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:45:07.095188+00:00
-- url     : https://prove2.me/submissions/6b9c1cef-ed72-426d-a757-0b6305d146b4

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.ghostOpN_add
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution (S T : Module.End ℂ (GhostSpace N)) :
    ghostOpN (S + T) = ghostOpN S + ghostOpN T := by
 simp [ghostOpN]
