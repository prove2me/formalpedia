-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.exwaF_Fil_0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:15.416228+00:00
-- url     : https://prove2.me/submissions/aa7f0405-3c4e-44fc-ad77-12f558a486b6

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
theorem _root_.solution (c : LL) (hc : c ≠ 0) (τ : ZMod n) : (exwaF c hc).Fil τ 0 = ⊥ := by
  simp [exwaF]
end Formalism.WeaklyAdmissibleFiltrations
