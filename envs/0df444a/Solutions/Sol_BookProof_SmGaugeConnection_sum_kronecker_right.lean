-- Prove2me | solution 1 for BookProof.SmGaugeConnection.sum_kronecker_right
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:10:53.910932+00:00
-- url     : https://prove2.me/submissions/cadb05e1-6a20-4dbf-b4f5-dd2888db5b0f

-- Generated from ChapterSmGaugeConnection.lean — solution of BookProof.SmGaugeConnection.sum_kronecker_right
import Mathlib
import Definitions.Def_ChapterSmGaugeConnection
import Definitions.Def_ChapterYangMillsSU3
import Definitions.Def_ChapterCPTHamiltonian
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterSmDiracSpinor
import Definitions.Def_ChapterFarisLavine
open BookProof.SmGaugeConnection




open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.ChapterCPTHamiltonian BookProof.SmCar
open BookProof.SmDiracYukawa BookProof.SmDiracSpinor BookProof.FarisLavine

noncomputable section

variable {N d : ℕ}

variable {N d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} (F : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ)
    (B : Matrix (Fin n) (Fin n) ℂ) : (∑ j : Fin 3, F j) ⊗ₖ B = ∑ j : Fin 3, (F j) ⊗ₖ B := by

  classical
  induction (Finset.univ : Finset (Fin 3)) using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_kronecker, ih]
