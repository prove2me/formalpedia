-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.ycond_full
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:47.622896+00:00
-- url     : https://prove2.me/submissions/cc471335-c4d4-40ee-a663-d5b3bc0072d8

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_ycond_stable
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_ycond_map
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_glAct_full_split
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_rest_comm
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_rest_supp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
variable [NeZero r]
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution (LL : Letters N) (j : ℕ) (M : WithTop ℤ) (c d : Fin r)
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hF : F ∈ YCond p LL j M) :
    glAct p LL N c d F ∈ YCond p LL j M := by
  rw [glAct_full_split p LL j c d, LinearMap.add_apply]
  exact add_mem (ycond_stable p LL j M c d F hF)
    (ycond_map p LL LL j j M (restAct p LL j c d)
      (fun c' d' G => rest_comm p LL j c d c' d' G)
      (fun G m hm => rest_supp p LL j c d G m hm) F hF)
end Formalism.GM.FrozenVariableComponents
