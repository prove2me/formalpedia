-- Prove2me | solution 1 for BookProof.QgHermiteFriedrichs.inner_pgLp_potLp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T12:43:10.633907+00:00
-- url     : https://prove2.me/submissions/8ec60dd4-7e71-479c-ae72-96977b628071

-- Generated from ChapterQgHermiteFriedrichs.lean — solution of BookProof.QgHermiteFriedrichs.inner_pgLp_potLp
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Theorems.Thm_BookProof_QgHermiteFriedrichs_potLp_coeFn
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
theorem solution (hWc : Continuous W) (hWb : ExpBounded W)
    (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp p) (potLp W hWc hWb q) : ℂ)
      = ∫ x : Vd d, (starRingEnd ℂ) (pgFun p x) * (((W x : ℝ) : ℂ) * pgFun q x) := by

  rw [inner_pgLp]
  refine integral_congr_ae ?_
  filter_upwards [potLp_coeFn W hWc hWb q] with x hx
  rw [hx]
