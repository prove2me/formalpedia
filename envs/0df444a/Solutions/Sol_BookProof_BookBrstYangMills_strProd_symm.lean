-- Prove2me | solution 1 for BookProof.BookBrstYangMills.strProd_symm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:42:52.455238+00:00
-- url     : https://prove2.me/submissions/756b1d74-02b7-442a-80a2-4a01ba5b1575

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.strProd_symm
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution (p q r s : Fin N) : strProd G p q r s = strProd G r s p q := Finset.sum_congr rfl fun _ _ => mul_comm _ _
