-- Prove2me | solution 1 for BookProof.BookBrstYangMills.strProd_swap34
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:42:54.671991+00:00
-- url     : https://prove2.me/submissions/3001a723-7147-4b01-b4d5-b058d8fa8304

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.strProd_swap34
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution (p q r s : Fin N) : strProd G p q r s = -strProd G p q s r := by

  simp only [strProd, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun m _ => by rw [G.antisymm r s m]; ring
