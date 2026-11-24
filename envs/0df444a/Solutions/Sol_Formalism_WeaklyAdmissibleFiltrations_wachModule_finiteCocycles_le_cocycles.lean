-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.wachModule_finiteCocycles_le_cocycles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:41:47.167811+00:00
-- url     : https://prove2.me/submissions/f208ec0f-3276-4d2b-931b-54c8c771a0c6

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_WachCol
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_wachModule_coboundaries_le_cocycles

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
open Formalism.CoboundaryTransfers
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {Bw : Base O A} {M : ℕ}
  {D D' : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  [AddCommGroup D'] [Module A D'] [Module O D'] [IsScalarTower O A D']
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution (W : WachMod Bw M D) : W.Zf ≤ W.Z1 := by
  unfold WachMod.Zf
  exact sup_le (Submodule.span_le.mpr (fun x hx => hx.1)) (wachModule_coboundaries_le_cocycles W)
end Formalism.WeaklyAdmissibleFiltrations
