-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.top_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:10.403913+00:00
-- url     : https://prove2.me/submissions/dafce09e-0b77-4c47-b201-af6cafcfa802

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_op_comm
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_top_apply
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
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution (LL : Letters N) (i i' : Fin N) (hi : i ≠ i') (c d c' d' : Fin r)
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    top p LL i c d (top p LL i' c' d' F) = top p LL i' c' d' (top p LL i c d F) := by
  have h1 : ∀ a b : Fin r, ((i, a) : Fin N × Fin r) ≠ (i', b) := fun a b h => hi (congrArg Prod.fst h)
  have h2 : ∀ a b : Fin r, ((i', a) : Fin N × Fin r) ≠ (i, b) := fun a b h => hi (congrArg Prod.fst h).symm
  simp only [top_apply]
  split_ifs <;> (try simp only [map_neg, mul_neg, neg_neg, neg_inj]) <;>
    exact op_comm _ _ _ _ (h1 _ _) (h2 _ _) F
end Formalism.GM.FrozenVariableComponents
