-- Prove2me | solution 1 for Formalism.L2.Th1.H.TaylorMvTens4_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:23:46.873751+00:00
-- url     : https://prove2.me/submissions/62a72c51-3203-4495-b483-c6d9639745d7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LineRestrLinSubst
import Theorems.Thm_Formalism_L2_Th1_H_TMv_lineRestr_block
import Theorems.Thm_Formalism_L2_Th1_H_TMv_analyticAt_clm
import Theorems.Thm_Formalism_L2_Th1_H_taylorMv_prod

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
theorem _root_.solution (hU : LineUnique) (hL : TaylorLine) : TaylorMvTens4 := by
  intro n _ _ θ hθ
  have hA : ∀ a : Fin 4, AnalyticAt ℂ (fun z : Fin 4 × n → ℂ => θ (slice a z)) 0 := fun a =>
    analyticAt_clm (ContinuousLinearMap.pi fun i : n =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 4 × n => ℂ) (a, i)) hθ
  have h := taylorMv_prod hU hL Finset.univ (fun (a : Fin 4) (z : Fin 4 × n → ℂ) => θ (slice a z)) hA
  refine Eq.trans h (Finset.prod_congr rfl fun a _ => ?_)
  refine hU ℂ (Fin 4 × n) _ _ fun v => ?_
  rw [hL _ _ (hA a) v, lineRestr_block, hL n θ hθ]
  rfl
end Formalism.L2.Th1.H
