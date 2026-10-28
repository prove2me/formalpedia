-- Prove2me | solution 2 for BookProof.SmHamiltonian.sm_friedrichs_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:13:21.978847+00:00
-- url     : https://prove2.me/submissions/196e720f-780c-4ffc-a42d-44c8590f1d37

import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
import Definitions.Def_ChapterSmHamiltonian
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterHermiteProductCore
import Theorems.Thm_BookProof_FriedrichsCanonical_friedrichsOp_isPositiveSelfAdjointExtension
import Theorems.Thm_BookProof_SmHamiltonian_smHamiltonian_symmetricOn
import Theorems.Thm_BookProof_SmHamiltonian_smHamiltonian_quadForm_nonneg
-- Generated from ChapterSmHamiltonian.lean — theorem solution
open BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs
open BookProof.SmHamiltonian



open MvPolynomial
open BookProof.SmOneParticle
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension

noncomputable section

variable {D : ℕ}
theorem solution (P : SmParams) :
    ∃ (Dom : Submodule ℂ (L2d 163)) (A : Dom →ₗ[ℂ] L2d 163),
      IsPositiveSelfAdjointExtension (smHamiltonian P) A := by
  let Q : BookProof.FriedrichsExtension.PosSymOp (L2d 163) :=
    { dom := BookProof.HermiteProductCore.polyGaussCore (d := 163)
      op := smHamiltonian P
      sym := smHamiltonian_symmetricOn P
      pos := fun x => smHamiltonian_quadForm_nonneg P x }
  exact ⟨_, _, BookProof.FriedrichsCanonical.friedrichsOp_isPositiveSelfAdjointExtension Q
    BookProof.HermiteProductCore.polyGaussCore_dense⟩
