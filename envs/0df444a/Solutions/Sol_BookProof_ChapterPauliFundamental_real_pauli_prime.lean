-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.real_pauli_prime
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:34.693654+00:00
-- url     : https://prove2.me/submissions/5b4ceaec-be72-44cb-be05-8f78479872d8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.real_pauli'
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Theorems.Thm_BookProof_ChapterPauliFundamental_pauliFundamental
import Theorems.Thm_BookProof_ChapterA3_real_pauli
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
import Definitions.Def_ChapterA3b
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution (α β : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ)
    (hα : IsCliffordR α) (hβ : IsCliffordR β) :
    ∃ S : Matrix (Fin 4) (Fin 4) ℝ, |S.det| = 1 ∧ (∀ μ, β μ = S * α μ * S⁻¹) ∧
      (∀ S' : Matrix (Fin 4) (Fin 4) ℝ, |S'.det| = 1 → (∀ μ, β μ = S' * α μ * S'⁻¹) →
        S' = S ∨ S' = -S) := real_pauli pauliFundamental α β hα hβ
