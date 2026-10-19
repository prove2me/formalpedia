-- Prove2me | solution 1 for BookProof.SmDiracSpinor.dirac_field_esa
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:35:20.808348+00:00
-- url     : https://prove2.me/submissions/b7c21601-d84c-4977-92cd-6f655860d91c

-- Generated from ChapterSmDiracSpinor.lean — solution of BookProof.SmDiracSpinor.dirac_field_esa
import Mathlib
import Definitions.Def_ChapterSmDiracSpinor
import Theorems.Thm_BookProof_SmDiracSpinor_diracOneParticle_hermitian
import Theorems.Thm_BookProof_SmDiracYukawa_sm_fermi_esa
import Definitions.Def_ChapterCPTHamiltonian
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
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
theorem solution {om : Fin 4 → ℝ} {c0 : ℝ} (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) :
    EssentiallySelfAdjointOn (fullDom 4)
      ((onFull (smFermiHam (diracOneParticle k m1 m2) (0 : Matrix (Fin 4) (Fin 4) ℂ) 0)).comp
        (Submodule.inclusion (le_refl (fullDom 4)))) := sm_fermi_esa (om := om) (c0 := c0) diracOneParticle_hermitian hom hc0
