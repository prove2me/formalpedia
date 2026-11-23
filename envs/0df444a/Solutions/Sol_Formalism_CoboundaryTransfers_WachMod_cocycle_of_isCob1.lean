-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.WachMod.cocycle_of_isCob1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:16.992334+00:00
-- url     : https://prove2.me/submissions/6cac85ad-53bf-41fa-9642-c0ede0ac187e

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_isOneCocycle_diffZero

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
theorem _root_.solution {y z : D} (h : W.IsCob1 y z) : W.Cocycle y z := by
  obtain ⟨x, hx, rfl, rfl⟩ := h; exact W.isOneCocycle_diffZero hx
end Formalism.CoboundaryTransfers.WachMod
