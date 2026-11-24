-- Prove2me | solution 1 for Formalism.L2.Th1.H.TaylorMvInj_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:03:21.161247+00:00
-- url     : https://prove2.me/submissions/caae3125-329e-4c8b-8ea3-689bbce2b932

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LineRestrLinSubst
import Theorems.Thm_Formalism_L2_Th1_H_TMv_analyticAt_line
import Theorems.Thm_Formalism_L2_Th1_F_taylorDeriv


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
theorem _root_.solution (_hU : LineUnique) (hL : TaylorLine) : TaylorMvInj := by
  intro n _ _ F G hF hG h
  funext v
  have hF' : AnalyticOnNhd ℂ (fun t : ℂ => F (t • v)) Set.univ := fun t _ =>
    analyticAt_line v (hF _ (Set.mem_univ _))
  have hG' : AnalyticOnNhd ℂ (fun t : ℂ => G (t • v)) Set.univ := fun t _ =>
    analyticAt_line v (hG _ (Set.mem_univ _))
  have hT : taylor0 (fun t : ℂ => F (t • v)) = taylor0 fun t : ℂ => G (t • v) := by
    rw [← hL n F (hF 0 (Set.mem_univ _)) v, ← hL n G (hG 0 (Set.mem_univ _)) v, h]
  have hE := taylorDeriv.2.2 _ _ (hF' 0 (Set.mem_univ _)) (hG' 0 (Set.mem_univ _)) hT
  have := congrFun (hF'.eq_of_eventuallyEq hG' hE) 1
  simpa using this
end Formalism.L2.Th1.H
