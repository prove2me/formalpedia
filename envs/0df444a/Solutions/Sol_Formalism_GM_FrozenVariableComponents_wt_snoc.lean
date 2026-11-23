-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.wt_snoc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:37.239829+00:00
-- url     : https://prove2.me/submissions/1e707ddf-9cd3-4746-b2fa-2e6e0f9b1a86

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_snoc_vec_castSucc
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
theorem _root_.solution (LL : Letters N) (n j : ℕ) (hj : j ≤ N) (c : Fin r) (m : Fin (N + 1) × Fin r →₀ ℕ) :
    wt (LL.snoc n) j c m = wt LL j c (llPart m) := by
  unfold Formalism.GM.M.wt
  rw [Fin.sum_univ_castSucc, if_neg (show ¬ ((Fin.last N : ℕ) < j) by rw [Fin.val_last]; omega), add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Fin.coe_castSucc, snoc_vec_castSucc, llPart_apply]
end Formalism.GM.FrozenVariableComponents
