-- Prove2me | solution 1 for BookProof.BookBrstYangMills.strProd_swap12
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:42:53.572099+00:00
-- url     : https://prove2.me/submissions/95f7d877-8759-4a16-9700-8bcff2df6e61

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.strProd_swap12
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution (p q r s : Fin N) : strProd G p q r s = -strProd G q p r s := by

  simp only [strProd, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun m _ => by rw [G.antisymm p q m]; ring
