-- Prove2me | solution 1 for BookProof.BookBrstYangMills.momPoly_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:46:41.666664+00:00
-- url     : https://prove2.me/submissions/c0e908e7-e97b-4650-8c38-a607e9ab7ade

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.momPoly_apply
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution (μ : Fin 4) (a : Fin N) (p : FieldPoly N) :
    momPoly μ a p = (-Complex.I) • (pderiv (μ, a) p) := rfl
