-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.ycond_hc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:02.794921+00:00
-- url     : https://prove2.me/submissions/2c3f823f-f162-4d8d-98a9-9b91b9421d86

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_glAct_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_ycond_map
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_op_hc
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
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
variable [NeZero r]
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution (LL : Letters N) (j : ℕ) (M : WithTop ℤ) (t : ℕ)
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hF : F ∈ YCond p LL j M) :
    homogeneousComponent t F ∈ YCond p LL j M := by
  refine ycond_map p LL LL j j M (homogeneousComponent t) (fun c d G => ?_) (fun G m hm => ?_) F hF
  · rw [glAct_apply, glAct_apply, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> simp [op_hc]
  · have h := mem_support_iff.1 hm
    rw [coeff_homogeneousComponent] at h
    split_ifs at h
    · exact ⟨m, mem_support_iff.2 h, rfl⟩
    · exact absurd rfl h
end Formalism.GM.FrozenVariableComponents
