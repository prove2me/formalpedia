-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.pderiv_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:12.392928+00:00
-- url     : https://prove2.me/submissions/7a6d2495-9960-416a-84d8-689e731ce163

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
variable {K : Type*} [CommRing K] {σ : Type*}
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution (a b : σ) (F : MvPolynomial σ K) :
    pderiv a (pderiv b F) = pderiv b (pderiv a F) := by
  classical
  refine MvPolynomial.induction_on' F (fun s c => ?_) (fun p q hp hq => ?_)
  · simp only [pderiv_monomial]
    by_cases hab : a = b
    · subst hab
      rfl
    · rw [show s - Finsupp.single b 1 - Finsupp.single a 1 = s - Finsupp.single a 1 - Finsupp.single b 1 from
        tsub_right_comm]
      congr 1
      rw [Finsupp.tsub_apply, Finsupp.tsub_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg hab,
        if_neg (Ne.symm hab), tsub_zero, tsub_zero]
      ring
  · simp only [map_add, hp, hq]
end Formalism.GM.FrozenVariableComponents
