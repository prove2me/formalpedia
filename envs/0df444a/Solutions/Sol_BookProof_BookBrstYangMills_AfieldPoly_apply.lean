-- Prove2me | solution 1 for BookProof.BookBrstYangMills.AfieldPoly_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:46:42.728731+00:00
-- url     : https://prove2.me/submissions/71602863-1bea-45a2-b856-1746c59753ad

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.AfieldPoly_apply
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution (μ : Fin 4) (a : Fin N) (p : FieldPoly N) :
    AfieldPoly μ a p = X (μ, a) * p := rfl
