-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.pht_window_mult_hi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:40:58.091466+00:00
-- url     : https://prove2.me/submissions/eec79515-c7c7-4705-994a-7d6ffb17ffe2

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_Window

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
variable {LL : Type} [Field LL] {D : Type} [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
  {n : ℕ} {Emb : Type} [Fintype Emb]
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution (F : FilPhi LL D n Emb) (D' : Submodule LL D) (τ : Emb) (a : ℤ)
    (ha : F.hi ≤ a) : F.mult D' τ a = 0 := by
  unfold FilPhi.mult
  rw [F.Fil_hi τ a ha, F.Fil_hi τ (a + 1) (by omega)]
  simp
end Formalism.WeaklyAdmissibleFiltrations
