-- Prove2me | solution 1 for Formalism.L2.Th1.H.TaylorMvMul_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:39:43.299798+00:00
-- url     : https://prove2.me/submissions/e28c2714-eb28-41bd-ba1b-35575772f645

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LineRestrLinSubst
import Theorems.Thm_Formalism_L2_Th1_H_TMv_lineRestr_mul
import Theorems.Thm_Formalism_L2_Th1_H_TMv_analyticAt_line0
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_mul
import Theorems.Thm_Formalism_L2_Th1_F_taylorRing


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
theorem _root_.solution (hU : LineUnique) (hL : TaylorLine) : TaylorMvMul := by
  intro n _ _ F G hF hG
  refine hU ℂ n _ _ fun v => ?_
  rw [hL n (fun z => F z * G z) (hF.mul hG) v, lineRestr_mul, hL n F hF v, hL n G hG v]
  exact (taylorRing.1 _ _ (analyticAt_line0 v hF) (analyticAt_line0 v hG)).2
end Formalism.L2.Th1.H
