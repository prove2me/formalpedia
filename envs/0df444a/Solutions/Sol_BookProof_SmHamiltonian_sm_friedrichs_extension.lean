-- Prove2me | solution 1 for BookProof.SmHamiltonian.sm_friedrichs_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:19:18.025563+00:00
-- url     : https://prove2.me/submissions/1490ee26-ca9e-4e07-9b4f-0e9bef55c6d6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSmHamiltonian.lean — solution of BookProof.SmHamiltonian.sm_friedrichs_extension
import Mathlib
import Definitions.Def_ChapterSmHamiltonian
import Theorems.Thm_BookProof_SmHamiltonian_smHamiltonian_symmetricOn
import Theorems.Thm_BookProof_SmHamiltonian_smHamiltonian_quadForm_nonneg
import Theorems.Thm_BookProof_FriedrichsExtension_friedrichs_extension_exists
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.SmHamiltonian




open MvPolynomial
open BookProof.SmOneParticle
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension

noncomputable section

variable {D : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (P : SmParams) :
    ∃ (Dom : Submodule ℂ (L2d 163)) (A : Dom →ₗ[ℂ] L2d 163),
      IsPositiveSelfAdjointExtension (smHamiltonian P) A :=
  friedrichs_extension_exists
      ⟨polyGaussCore, smHamiltonian P, smHamiltonian_symmetricOn P,
        smHamiltonian_quadForm_nonneg P⟩
      polyGaussCore_dense
