-- Prove2me | solution 1 for BookProof.ShiftedQuadratic.shiftedHOp_coe_eq_pgLpT
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:41:25.846846+00:00
-- url     : https://prove2.me/submissions/28cb9d5b-5480-4750-83be-4accbf9f170b

-- Generated from ChapterShiftedQuadraticEsa.lean — solution of BookProof.ShiftedQuadratic.shiftedHOp_coe_eq_pgLpT
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Theorems.Thm_BookProof_ShiftedHermiteCore_coreOpT_coe
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.ShiftedQuadratic




open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.ShiftedHermiteCore
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (a k : Vd d) (c b b' : Fin d → ℝ)
    (p : MvPolynomial (Fin d) ℂ) :
    shiftedHOp a k c b b' (coreEquivT a k p) = pgLpT a k (shiftedHPoly a k c b b' p) := by

  simp only [shiftedHOp, LinearMap.comp_apply, Submodule.subtype_apply]
  rw [coreOpT_coe]
