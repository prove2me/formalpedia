-- Prove2me | solution 1 for Formalism.GM.extendMapsTo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:33.2678+00:00
-- url     : https://prove2.me/submissions/6bcd4002-0f26-4120-9c8b-79dc9447b830

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_freeze_mem_pol
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_freeze_inv
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_freeze_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
namespace Formalism.GM
theorem _root_.solution : M.FreezeInto := by
  intro p _ N r LL ρ n hn f hf
  exact ⟨FrozenVariableLemmas.freeze_mem_pol p LL ρ n hn hf, FrozenVariableLemmas.freeze_inv p LL ρ n f,
    fun h => FrozenVariableLemmas.freeze_int p LL ρ n h⟩
end Formalism.GM
