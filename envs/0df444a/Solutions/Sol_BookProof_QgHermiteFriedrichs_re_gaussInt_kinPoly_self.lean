-- Prove2me | solution 1 for BookProof.QgHermiteFriedrichs.re_gaussInt_kinPoly_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T13:21:05.471305+00:00
-- url     : https://prove2.me/submissions/252e0018-d81b-407d-934e-be891ff8d64a

-- Generated from ChapterQgHermiteFriedrichs.lean — solution of BookProof.QgHermiteFriedrichs.re_gaussInt_kinPoly_self
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Theorems.Thm_BookProof_QgHermiteFriedrichs_inner_pgLp_pgLp
import Theorems.Thm_BookProof_QgHermiteFriedrichs_gaussInt_kinPoly
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
theorem solution (p : MvPolynomial (Fin d) ℂ) :
    (gaussInt (cpoly p * kinPoly p)).re = ∑ j : Fin d, ‖pgLp (coreD j p)‖ ^ 2 := by

  rw [gaussInt_kinPoly]
  have h : ∀ j : Fin d, gaussInt (cpoly (coreD j p) * coreD j p)
      = ((‖pgLp (coreD j p)‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    rw [← inner_pgLp_pgLp, inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    norm_cast
  simp only [h, ← Complex.ofReal_sum, Complex.ofReal_re]
