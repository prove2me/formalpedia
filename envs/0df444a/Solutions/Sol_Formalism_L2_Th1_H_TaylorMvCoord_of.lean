-- Prove2me | solution 1 for Formalism.L2.Th1.H.TaylorMvCoord_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:52:35.884317+00:00
-- url     : https://prove2.me/submissions/8ba0f7fb-697d-47fb-bb2c-a50816df59cd

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LineRestrLinSubst
import Theorems.Thm_Formalism_L2_Th1_H_TMv_lineRestr_at1_eq_rescale
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
theorem _root_.solution (hU : LineUnique) (hL : TaylorLine) : TaylorMvCoord := by
  intro n _ _ i f hf
  refine hU ℂ n _ _ fun v => ?_
  have hA : AnalyticAt ℂ (fun z : n → ℂ => f (z i)) 0 :=
    hf.comp_of_eq ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) i).analyticAt 0) rfl
  rw [hL n _ hA v, lineRestr_at1_eq_rescale, ← taylorDeriv.2.1 f (v i) hf]
  simp only [Pi.smul_apply, smul_eq_mul, mul_comm]
end Formalism.L2.Th1.H
