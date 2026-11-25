-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.WachMod.finiteCocycles_le_cocycles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:47:58.012518+00:00
-- url     : https://prove2.me/submissions/f44ad582-8c76-4728-b84b-d39e8e3ca65e

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_coboundaries_le_cocycles

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
open Formalism.CoboundaryTransfers.WachMod
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  (W : WachMod B M D)
namespace Formalism.CoboundaryTransfers.WachMod
theorem _root_.solution : W.Zf ≤ W.Z1 :=
  sup_le (Submodule.span_le.2 fun _ h => h.1) W.coboundaries_le_cocycles
end Formalism.CoboundaryTransfers.WachMod
