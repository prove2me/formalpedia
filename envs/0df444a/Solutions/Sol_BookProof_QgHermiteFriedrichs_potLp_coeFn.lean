-- Prove2me | solution 1 for BookProof.QgHermiteFriedrichs.potLp_coeFn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T08:00:45.99945+00:00
-- url     : https://prove2.me/submissions/d8f381e8-8461-4a28-9852-9b48a7434049

-- Generated from ChapterQgHermiteFriedrichs.lean — solution of BookProof.QgHermiteFriedrichs.potLp_coeFn
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
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
theorem solution (hWc : Continuous W) (hWb : ExpBounded W) (p : MvPolynomial (Fin d) ℂ) :
    (potLp W hWc hWb p : Vd d → ℂ) =ᵐ[volume] fun x => ((W x : ℝ) : ℂ) * pgFun p x := (memLp_mul_pgFun_of_expBounded hWc hWb p).coeFn_toLp
