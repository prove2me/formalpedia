-- Prove2me | solution 1 for BookProof.BookBrstYangMills.bosOpN_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:44:53.407548+00:00
-- url     : https://prove2.me/submissions/e4e54ac4-af22-4d7e-96f3-33674b0e9f61

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.bosOpN_sum
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} (T : Fin n → Module.End ℂ (FieldPoly N)) :
    bosOpN (∑ e, T e) = ∑ e, bosOpN (T e) := map_sum (LinearMap.rTensorHom (R := ℂ) (GhostSpace N)) T Finset.univ
