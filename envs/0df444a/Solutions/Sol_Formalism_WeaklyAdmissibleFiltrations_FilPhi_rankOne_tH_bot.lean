-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.FilPhi.rankOne_tH_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:40:56.133039+00:00
-- url     : https://prove2.me/submissions/55ea1f38-620d-4e22-9187-27328edbe470

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_RankOne

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
open Formalism.WeaklyAdmissibleFiltrations.FilPhi
variable {LL : Type} [Field LL] {D : Type} [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
  {n : ℕ} {Emb : Type} [Fintype Emb]
namespace Formalism.WeaklyAdmissibleFiltrations.FilPhi
theorem _root_.solution (F : FilPhi LL D n Emb) : F.tH ⊥ = 0 := by
  have h0 : ∀ S : Submodule LL D, finrank LL ↥(S ⊓ ⊥) = 0 := fun S => by
    rw [Submodule.finrank_eq_zero]; exact inf_bot_eq S
  simp [tH, tHw, mult, h0]
end Formalism.WeaklyAdmissibleFiltrations.FilPhi
