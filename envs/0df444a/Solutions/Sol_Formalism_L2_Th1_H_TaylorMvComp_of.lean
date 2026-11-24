-- Prove2me | solution 1 for Formalism.L2.Th1.H.TaylorMvComp_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:25:20.351244+00:00
-- url     : https://prove2.me/submissions/df695c29-78d9-4176-a66a-8cf8facd5b80

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LineRestrLinSubst
import Theorems.Thm_Formalism_L2_Th1_H_TMv_lineRestr_linSubst
import Theorems.Thm_Formalism_L2_Th1_H_TMv_analyticAt_clm

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open TMv Formalism.L2.Th1.F
namespace Formalism.L2.Th1.H
theorem _root_.solution (hU : LineUnique) (hL : TaylorLine) : TaylorMvComp := by
  intro m n _ _ _ _ M F hF
  refine hU ℂ n _ _ fun v => ?_
  have hA : AnalyticAt ℂ (fun w : n → ℂ => F (M.mulVec w)) 0 :=
    analyticAt_clm (LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)) hF
  rw [hL n _ hA v, lineRestr_linSubst, hL m F hF]
  simp only [Matrix.mulVec_smul]
end Formalism.L2.Th1.H
