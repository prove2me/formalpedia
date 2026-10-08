-- Prove2me | solution 1 for BookProof.BookBrstYangMills.bosOpN_sum3
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:47:55.45198+00:00
-- url     : https://prove2.me/submissions/ec910f2f-89b8-494e-9e47-c15b939dcaff

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.bosOpN_sum3
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
import Theorems.Thm_BookProof_BookBrstYangMills_bosOpN_sum
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution (T : Fin 4 → Fin N → Fin N → Module.End ℂ (FieldPoly N)) :
    bosOpN (∑ μ, ∑ a, ∑ b, T μ a b) = ∑ μ, ∑ a, ∑ b, bosOpN (T μ a b) := by

  rw [bosOpN_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [bosOpN_sum]
  exact Finset.sum_congr rfl fun a _ => bosOpN_sum _
