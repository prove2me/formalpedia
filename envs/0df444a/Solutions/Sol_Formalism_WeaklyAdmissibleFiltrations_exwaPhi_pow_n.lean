-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.exwaPhi_pow_n
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:54:13.493795+00:00
-- url     : https://prove2.me/submissions/b61d49b2-e3ba-4b73-9a83-35232722a342

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExwaFiltrationNegOneEqSpanSingle
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaPhi_pow_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module
variable {LL : Type} [Field LL] {n : ℕ} [NeZero n]
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution (c : LL) (hc : c ≠ 0) :
    (exwaPhi (n := n) c hc).toLinearMap ^ n = c ^ n • 1 := by
  refine LinearMap.ext fun x => ?_
  rw [exwaPhi_pow_apply, ZMod.natCast_self]
  simp
end Formalism.WeaklyAdmissibleFiltrations
