-- Prove2me | solution 1 for Formalism.L2.Th1.F.th0Const_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:46.749204+00:00
-- url     : https://prove2.me/submissions/3834eab4-917e-4a16-b840-4c40bfe2df25

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HermHalfRight
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroHermitianLemmas_herm_zero_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open ThetaZeroHermitianLemmas
namespace Formalism.L2.Th1.F
theorem _root_.solution (hb : SgStarBasic) : ThetaZeroConstant := by
  intro L t
  have h : opU L t (sgStar L) 0 = sgStar L t * Complex.exp (-(Real.pi : ℂ) * herm L t t / 2) := by
    simp only [opU, zero_add, herm_zero_left]; congr 2; ring
  refine ⟨h, fun ht => ?_⟩
  rw [h]
  exact mul_ne_zero (fun h0 => ht (((hb L).2.2.1 t).1 h0)) (Complex.exp_ne_zero _)
end Formalism.L2.Th1.F
