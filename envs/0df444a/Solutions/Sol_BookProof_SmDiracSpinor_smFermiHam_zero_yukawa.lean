-- Prove2me | solution 1 for BookProof.SmDiracSpinor.smFermiHam_zero_yukawa
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:35:18.746875+00:00
-- url     : https://prove2.me/submissions/27bccbaf-6397-4de5-afc1-5e4f2e3ebdcd

-- Generated from ChapterSmDiracSpinor.lean — solution of BookProof.SmDiracSpinor.smFermiHam_zero_yukawa
import Mathlib
import Definitions.Def_ChapterSmDiracSpinor
import Definitions.Def_ChapterCPTHamiltonian
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterSmDiracYukawa
open BookProof.SmDiracSpinor




open Matrix
open BookProof.ChapterCPTHamiltonian BookProof.SmCar BookProof.SmDiracYukawa
open BookProof.FarisLavine

noncomputable section

variable {k : Fin 3 → ℝ} {m1 m2 : ℝ}

variable {k : Fin 3 → ℝ} {m1 m2 : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hD : Matrix (Fin 4) (Fin 4) ℂ) :
    smFermiHam hD (0 : Matrix (Fin 4) (Fin 4) ℂ) 0 = fermiBilin hD := by

  simp [smFermiHam, smFermiMatrix]
