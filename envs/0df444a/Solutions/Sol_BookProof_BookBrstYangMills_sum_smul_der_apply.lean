-- Prove2me | solution 1 for BookProof.BookBrstYangMills.sum_smul_der_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:47:18.771152+00:00
-- url     : https://prove2.me/submissions/094cc836-b92f-4e81-ab65-bd63812807c6

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.sum_smul_der_apply
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} (k : Fin n → ℂ)
    (D : Fin n → Derivation ℂ (FieldPoly N) (FieldPoly N)) (p : FieldPoly N) :
    (∑ h, k h • D h) p = ∑ h, k h • (D h) p := by

  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply,
        Derivation.smul_apply, ih]
