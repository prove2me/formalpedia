-- Prove2me | solution 1 for Formalism.L2.Th1.H.TaylorMvLinear_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:21:01.644373+00:00
-- url     : https://prove2.me/submissions/10d628ad-df3c-453f-9f21-cfddec3f61f0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LineRestrLinSubst
import Theorems.Thm_Formalism_L2_Th1_H_TMv_lineRestr_add
import Theorems.Thm_Formalism_L2_Th1_H_TMv_lineRestr_mul
import Theorems.Thm_Formalism_L2_Th1_H_TMv_lineRestr_C
import Theorems.Thm_Formalism_L2_Th1_H_TMv_analyticAt_line0
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_add
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_add
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
theorem _root_.solution (hU : LineUnique) (hL : TaylorLine) : TaylorMvLinear := by
  intro n _ _ F G hF hG
  refine ⟨hU ℂ n _ _ fun v => ?_, fun c => hU ℂ n _ _ fun v => ?_⟩
  · rw [hL n (fun z => F z + G z) (hF.add hG) v, lineRestr_add, hL n F hF v, hL n G hG v]
    exact (taylorRing.1 _ _ (analyticAt_line0 v hF) (analyticAt_line0 v hG)).1
  · rw [hL n (fun z => c * F z) (analyticAt_const.mul hF) v, lineRestr_mul, lineRestr_C, hL n F hF v,
      ← taylorRing.2.1 c]
    exact (taylorRing.1 _ _ analyticAt_const (analyticAt_line0 v hF)).2
end Formalism.L2.Th1.H
