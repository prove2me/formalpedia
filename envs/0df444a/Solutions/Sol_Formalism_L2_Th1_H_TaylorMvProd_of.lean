-- Prove2me | solution 1 for Formalism.L2.Th1.H.TaylorMvProd_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:23:45.315048+00:00
-- url     : https://prove2.me/submissions/0b95f344-1bb7-4cc3-9a09-398bbbd7a0fe

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LineRestrLinSubst
import Theorems.Thm_Formalism_L2_Th1_H_TaylorMvCoord_of
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
theorem _root_.solution (hU : LineUnique) (hL : TaylorLine) : TaylorMvProd := by
  intro n _ _ f hf
  have h := taylorMv_prod hU hL Finset.univ (fun (i : n) (z : n → ℂ) => f i (z i)) fun i =>
    (hf i).comp_of_eq ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) i).analyticAt 0) rfl
  refine Eq.trans h (Finset.prod_congr rfl fun i _ => ?_)
  exact TaylorMvCoord_of hU hL n i (f i) (hf i)
end Formalism.L2.Th1.H
