-- Prove2me | solution 1 for BookProof.YangMillsAbelianEsa.sum_ymMagVec_mulX
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T17:53:04.029813+00:00
-- url     : https://prove2.me/submissions/8e43677c-eb1c-4f18-8932-27f6b646bc31

-- Generated from ChapterYangMillsAbelianEsa.lean — theorem BookProof.YangMillsAbelianEsa.sum_ymMagVec_mulX
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Theorems.Thm_BookProof_YangMillsAbelianEsa_sum_ymMagVec_X
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_mulXPoly_apply
import Definitions.Def_ChapterYangMillsAbelianEsa
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterYangMillsHermite
open BookProof.ChapterF7
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.YangMillsHermite
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
theorem ym_magX_aux (m : Fin 24) :
    ∑ n : Fin 99, ((ymMagVec m n : ℝ) : ℂ) • mulXPoly (d := 99) n
      = mulOp (magPoly 0 (decodeSpace m) (decodeColor m)) := by
  refine LinearMap.ext fun q => ?_
  rw [← BookProof.YangMillsAbelianEsa.sum_ymMagVec_X m]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, BookProof.NavierStokesFlow.DifferentialL2.mulXPoly_apply,
    BookProof.YangMillsHermite.mulOp, LinearMap.mulLeft_apply, Finset.sum_mul, smul_mul_assoc]

open BookProof BookProof.YangMillsAbelianEsa in
theorem solution (m : Fin 24) :
    ∑ n : Fin 99, ((ymMagVec m n : ℝ) : ℂ) • mulXPoly (d := 99) n
      = mulOp (magPoly 0 (decodeSpace m) (decodeColor m)) := by 
  exact ym_magX_aux m
