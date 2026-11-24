-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.exwa_nsmul_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:40:50.614791+00:00
-- url     : https://prove2.me/submissions/ad2c1e91-ed0f-4f41-bb2e-587e2aa8f4d0

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
variable {LL : Type} [Field LL]
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution (k : ℕ) (hk : k ≠ 0) : k • (⊤ : WithTop ℚ) = ⊤ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [succ_nsmul, WithTop.add_top]
end Formalism.WeaklyAdmissibleFiltrations
