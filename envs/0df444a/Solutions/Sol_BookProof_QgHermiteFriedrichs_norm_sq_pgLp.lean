-- Prove2me | solution 1 for BookProof.QgHermiteFriedrichs.norm_sq_pgLp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T12:43:09.76239+00:00
-- url     : https://prove2.me/submissions/81925b6e-3dea-4ab1-a114-f97a4c21f876

-- Generated from ChapterQgHermiteFriedrichs.lean — solution of BookProof.QgHermiteFriedrichs.norm_sq_pgLp
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Theorems.Thm_BookProof_QgHermiteFriedrichs_conj_mul_self
import Theorems.Thm_BookProof_QgHermiteFriedrichs_inner_L2_eq
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
    ‖pgLp p‖ ^ 2 = ∫ x : Vd d, ‖pgFun p x‖ ^ 2 := by

  have h1 : (inner ℂ (pgLp p) (pgLp p) : ℂ) = ((∫ x : Vd d, ‖pgFun p x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_L2_eq, ← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [pgLp_coeFn p] with x hx
    rw [hx, conj_mul_self]
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)] at h1
  refine Complex.ofReal_inj.mp ?_
  push_cast
  exact h1
