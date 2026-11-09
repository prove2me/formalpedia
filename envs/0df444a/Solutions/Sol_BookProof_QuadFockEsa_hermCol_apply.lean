-- Prove2me | solution 1 for BookProof.QuadFockEsa.hermCol_apply
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T21:09:26.47019+00:00
-- url     : https://prove2.me/submissions/c9d05098-ebc4-4161-97ca-2b5de349c198
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterQuadraticFockEsa.lean — solution of BookProof.QuadFockEsa.hermCol_apply
import Mathlib
import Definitions.Def_ChapterQuadraticFockEsa
import Theorems.Thm_BookProof_QuadFockEsa_symm_equiv_hermBasisN
import Theorems.Thm_BookProof_FockSecondQuantization_opCol_apply
import Theorems.Thm_BookProof_YangMillsHermite_CoreRep_coe_op
import Definitions.Def_ChapterGradedBandSchurEsa
import Definitions.Def_ChapterGradedBandSchurEsaPromoted
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
open BookProof.QuadFockEsa




open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.GradedBandSchur
open BookProof.FockSecondQuantization BookProof.NavierStokesFlow
open BookProof.HermiteGalerkin BookProof.FarisLavine
open BookProof.YangMillsHermite BookProof.FullQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.FockSecondQuantization
open BookProof.HermiteBand
open BookProof.HermiteGalerkin
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (e : ℕ ≃ (Fin d →₀ ℕ)) (T : Module.End ℂ (MvPolynomial (Fin d) ℂ))
    (k j : ℕ) :
    hermCol e T k j = (inner ℂ (hermiteMvLp (e j)) (pgLp (T (hpsi (e k)))) : ℂ) := by

  rw [hermCol, opCol_apply, CoreRep.coe_op, symm_equiv_hermBasisN, hermBasisN_apply]
