-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.exwaF_Dl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:40:59.772402+00:00
-- url     : https://prove2.me/submissions/66a63b21-3a3c-4aec-b3d8-934bf44c59ca

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExwaFiltrationNegOneEqSpanSingle

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
theorem _root_.solution (c : LL) (hc : c ≠ 0) (i : ZMod n) :
    (exwaF c hc).Dl i = LL ∙ (Pi.single i (1 : LL) : ZMod n → LL) := rfl
end Formalism.WeaklyAdmissibleFiltrations
