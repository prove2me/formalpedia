-- Prove2me | solution 1 for Formalism.L2.Th1.H.taylorMv_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:02:50.434296+00:00
-- url     : https://prove2.me/submissions/8e811e80-3c11-4e55-83f8-6f74dcae3597

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LineRestrLinSubst
import Theorems.Thm_Formalism_L2_Th1_H_TMv_lineRestr_one
import Theorems.Thm_Formalism_L2_Th1_H_TaylorMvMul_of
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
theorem _root_.solution (hU : LineUnique) (hL : TaylorLine) {n : Type} [Fintype n] [DecidableEq n]
    {ι : Type} (s : Finset ι) (F : ι → (n → ℂ) → ℂ) (hF : ∀ i, AnalyticAt ℂ (F i) 0) :
    taylorMv (fun z => ∏ i ∈ s, F i z) = ∏ i ∈ s, taylorMv (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    refine hU ℂ n _ _ fun v => ?_
    rw [hL n _ analyticAt_const v, lineRestr_one, taylorRing.2.1 1, map_one]
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    rw [TaylorMvMul_of hU hL n (F a) _ (hF a) (Finset.analyticAt_fun_prod s fun i _ => hF i), ih]
end Formalism.L2.Th1.H
