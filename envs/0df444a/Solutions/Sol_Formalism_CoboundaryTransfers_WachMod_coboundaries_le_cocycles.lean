-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.WachMod.coboundaries_le_cocycles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:39:00.476552+00:00
-- url     : https://prove2.me/submissions/c2a7d185-576b-415a-8fcd-82e52d718b21

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_diffOne_diffZero
import Theorems.Thm_P2M_Formalism_CoboundaryTransfers_WachMod_mem_cocycles__3712a15bf5f6

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
theorem _root_.solution : W.B1 ≤ W.Z1 := by
  rintro _ ⟨x, rfl⟩
  rw [W.mem_cocycles']
  simpa [LinearMap.prod_apply] using W.diffOne_diffZero x
end Formalism.CoboundaryTransfers.WachMod
