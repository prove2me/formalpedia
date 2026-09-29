-- Prove2me | solution 1 for BookProof.QgHermiteFriedrichs.hasDerivAt_pgFun_coord
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T13:21:04.614214+00:00
-- url     : https://prove2.me/submissions/42788146-78a6-43da-bfbc-c966c69d6625

-- Generated from ChapterQgHermiteFriedrichs.lean — solution of BookProof.QgHermiteFriedrichs.hasDerivAt_pgFun_coord
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Theorems.Thm_BookProof_QgHermiteFriedrichs_coordLine_self
import Theorems.Thm_BookProof_QgHermiteFriedrichs_hasDerivAt_gaussD_coordLine
import Theorems.Thm_BookProof_QgHermiteFriedrichs_hasDerivAt_polyEval_coordLine
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFarisLavine
open BookProof.QgHermiteFriedrichs








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}































variable (W : Vd d → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (p : MvPolynomial (Fin d) ℂ) (j : Fin d) (x : Vd d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => pgFun p (coordLine x j s))
      (pgFun (coreD j p) (coordLine x j t)) t := by

  have hE := hasDerivAt_polyEval_coordLine p x j t
  have hg := (hasDerivAt_gaussD_coordLine x j t).ofReal_comp
  have hmul := hE.mul hg
  refine hmul.congr_deriv ?_
  simp only [pgFun, coreD, map_sub, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C,
    coordLine_self]
  push_cast
  ring
