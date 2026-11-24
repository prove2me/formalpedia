-- Prove2me | solution 1 for Formalism.GM.M.FB.ev_freezeSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:42.124858+00:00
-- url     : https://prove2.me/submissions/7ff24210-cd82-463a-8d5e-76b08d323c59

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.M.FB
theorem _root_.solution (LL : Letters N) (ρ : Fin r) (v : Fin N × Fin r) :
    ev p ρ (freezeSub p LL ρ v) = X v := by
  rcases v with ⟨i, c⟩
  by_cases hv : LL.vec i <;> by_cases hc : c = ρ <;>
    simp [freezeSub, ev, hv, hc, mul_ite, Finset.sum_ite_eq']
end Formalism.GM.M.FB
