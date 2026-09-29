-- Prove2me | solution 1 for BookProof.QgHermiteFriedrichs.inner_pgLp_pgLp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T13:20:50.010777+00:00
-- url     : https://prove2.me/submissions/b3e25a83-0df0-4e87-b27a-dcc63339f334

-- Generated from ChapterQgHermiteFriedrichs.lean — solution of BookProof.QgHermiteFriedrichs.inner_pgLp_pgLp
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Theorems.Thm_BookProof_QgHermiteFriedrichs_conj_pgFun
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFarisLavine
open BookProof.QgHermiteFriedrichs








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp p) (pgLp q) : ℂ) = gaussInt (cpoly p * q) := by

  rw [inner_pgLp, gaussInt]
  refine integral_congr_ae ?_
  filter_upwards [pgLp_coeFn q] with x hx
  rw [hx, conj_pgFun]
  simp only [pgFun, map_mul, gaussWD_eq_sq]
  push_cast
  ring
