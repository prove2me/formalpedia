-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.exwa_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:16.187807+00:00
-- url     : https://prove2.me/submissions/cd18eb65-9c05-4b1b-8332-a0c1fe77e04d

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
theorem _root_.solution : finrank LL (ZMod n → LL) = n := by
  rw [Module.finrank_fintype_fun_eq_card, ZMod.card n]
end Formalism.WeaklyAdmissibleFiltrations
