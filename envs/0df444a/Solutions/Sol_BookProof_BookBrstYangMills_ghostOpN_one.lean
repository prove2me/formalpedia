-- Prove2me | solution 1 for BookProof.BookBrstYangMills.ghostOpN_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:45:20.654491+00:00
-- url     : https://prove2.me/submissions/fdc85a28-b82a-4890-afde-93c17c746acf

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.ghostOpN_one
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution : ghostOpN (1 : Module.End ℂ (GhostSpace N)) = 1 := by

  simp [ghostOpN, Module.End.one_eq_id, LinearMap.lTensor_id]
