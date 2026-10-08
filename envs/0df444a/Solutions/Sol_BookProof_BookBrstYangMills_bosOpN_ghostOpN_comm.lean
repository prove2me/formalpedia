-- Prove2me | solution 1 for BookProof.BookBrstYangMills.bosOpN_ghostOpN_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:46:18.581075+00:00
-- url     : https://prove2.me/submissions/93ba4fd5-5fa5-4d64-8123-db7acdd77294

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.bosOpN_ghostOpN_comm
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution (S : Module.End ℂ (FieldPoly N)) (T : Module.End ℂ (GhostSpace N)) :
    bosOpN S * ghostOpN T = ghostOpN T * bosOpN S := by

  simp [bosOpN, ghostOpN, Module.End.mul_eq_comp, LinearMap.lTensor_comp_rTensor,
    LinearMap.rTensor_comp_lTensor]
