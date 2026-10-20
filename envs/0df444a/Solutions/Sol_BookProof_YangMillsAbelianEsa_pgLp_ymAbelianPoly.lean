-- Prove2me | solution 1 for BookProof.YangMillsAbelianEsa.pgLp_ymAbelianPoly
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T17:53:27.145992+00:00
-- url     : https://prove2.me/submissions/2556cf31-bb2e-4fcb-8356-d8e67ac9bcc8

-- Generated from ChapterYangMillsAbelianEsa.lean — theorem BookProof.YangMillsAbelianEsa.pgLp_ymAbelianPoly
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
import Theorems.Thm_BookProof_YangMillsAbelianEsa_pgLp_eq_pgMap
import Definitions.Def_ChapterYangMillsAbelianEsa
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterYangMillsHermite
open BookProof.ChapterF7
open BookProof.HermiteProductCore
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
theorem ym_apply_aux (p : MvPolynomial (Fin 99) ℂ) :
    ymAbelianPoly p
      = ((1 / 2 : ℝ) : ℂ)
        • ((∑ m : Fin 24,
              BookProof.YangMillsHermite.momOp (ymMomIdx m) (BookProof.YangMillsHermite.momOp (ymMomIdx m) p))
            + ∑ m : Fin 24, mulOp (magPoly 0 (decodeSpace m) (decodeColor m))
                (mulOp (magPoly 0 (decodeSpace m) (decodeColor m)) p)) := by
  simp only [ymAbelianPoly, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.comp_apply]

open BookProof BookProof.YangMillsAbelianEsa in
theorem solution (p : MvPolynomial (Fin 99) ℂ) :
    pgLp (ymAbelianPoly p)
      = ((1 / 2 : ℝ) : ℂ)
        • ((∑ m : Fin 24, pgLp (YangMillsHermite.momOp (ymMomIdx m)
              (YangMillsHermite.momOp (ymMomIdx m) p)))
            + ∑ m : Fin 24, pgLp (mulOp (magPoly 0 (decodeSpace m) (decodeColor m))
                (mulOp (magPoly 0 (decodeSpace m) (decodeColor m)) p))) := by 
  rw [ym_apply_aux]
  simp only [BookProof.YangMillsAbelianEsa.pgLp_eq_pgMap, map_smul, map_add, map_sum]
