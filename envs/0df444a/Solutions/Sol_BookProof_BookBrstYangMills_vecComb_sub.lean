-- Prove2me | solution 1 for BookProof.BookBrstYangMills.vecComb_sub
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:46:54.428539+00:00
-- url     : https://prove2.me/submissions/bcc49eb6-2ca8-42e7-9d90-31bac12d2a7b

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.vecComb_sub
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution (α α' : ℝ) (β β' : Fin N → ℝ) (μ : Fin 4) :
    vecComb α β μ - vecComb α' β' μ = vecComb (α - α') (fun g => β g - β' g) μ := by

  simp only [vecComb, Complex.ofReal_sub, sub_smul, Finset.sum_sub_distrib]
  abel
