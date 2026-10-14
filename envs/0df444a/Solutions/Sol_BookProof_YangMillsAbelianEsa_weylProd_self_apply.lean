-- Prove2me | solution 1 for BookProof.YangMillsAbelianEsa.weylProd_self_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:06:03.064837+00:00
-- url     : https://prove2.me/submissions/11009d56-f80a-430c-b73a-9672380e3780

-- Generated from ChapterYangMillsAbelianEsa.lean — solution of BookProof.YangMillsAbelianEsa.weylProd_self_apply
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsAbelianEsa




open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {d : ℕ} (S : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (p : MvPolynomial (Fin d) ℂ) : weylProd S S p = S (S p) := by

  simp only [weylProd, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply]
  rw [← two_smul ℂ (S (S p)), smul_smul]
  norm_num
