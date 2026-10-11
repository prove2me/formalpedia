-- Prove2me | solution 1 for BookProof.SmGaugeConnection.covD_conj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:09:45.609973+00:00
-- url     : https://prove2.me/submissions/6c7aae0f-3763-4f75-9076-2451cae1fed7

-- Generated from ChapterSmGaugeConnection.lean — solution of BookProof.SmGaugeConnection.covD_conj
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
theorem solution {k : Fin 3 → ℝ} {g : ℝ} {T : Fin d → Matrix (Fin N) (Fin N) ℂ}
    {A : Fin d → Fin 3 → ℝ} {U : Matrix (Fin N) (Fin N) ℂ} (hU : U * Uᴴ = 1) (j : Fin 3) :
    U * covD k g T A j * Uᴴ
      = Complex.I • (((k j : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)
          + U * conn g T A j * Uᴴ) := by

  rw [covD, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU]
