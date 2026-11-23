-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.glAct_full_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:37.541558+00:00
-- url     : https://prove2.me/submissions/d3d92783-9ec1-49b1-98fe-292c538e30df

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_glAct_full_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableLemmas
open MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {K r : ℕ} (L : M.Letters K) (c ρ : Fin r)
namespace Formalism.GM.FrozenVariableLemmas
theorem _root_.solution (a : ℚ_[p]) : M.glAct p L K c ρ (C a) = 0 := by
  rw [glAct_full_apply]
  simp
end Formalism.GM.FrozenVariableLemmas
