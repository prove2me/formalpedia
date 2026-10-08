-- Prove2me | solution 1 for BookProof.BookBrstYangMills.pderiv_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:47:19.883707+00:00
-- url     : https://prove2.me/submissions/27fc1964-2593-4524-8469-7c61cd2c7111

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.pderiv_X_mul
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution (i j : Fin 4 × Fin N) (p : FieldPoly N) :
    (pderiv i : Derivation ℂ (FieldPoly N) (FieldPoly N)) (X j * p)
      = (if i = j then p else 0) + X j * pderiv i p := by

  classical
  rw [Derivation.leibniz]
  simp only [MvPolynomial.pderiv_X, Pi.single_apply]
  by_cases h : i = j
  · subst h; simp; ring
  · rw [if_neg h, if_neg (fun hc => h hc.symm)]
    simp
