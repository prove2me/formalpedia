-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.WachMod.mem_coboundaries_of_isOneCoboundary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:17.132182+00:00
-- url     : https://prove2.me/submissions/9ba4fe5a-bfbd-47c5-8a1d-4f03a71bf1a7

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_diffZero_mem_coboundaries

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
theorem _root_.solution {y z : D} (h : W.IsCob1 y z) : (y, z) ∈ W.B1 := by
  obtain ⟨x, _, rfl, rfl⟩ := h; exact W.diffZero_mem_coboundaries x
end Formalism.CoboundaryTransfers.WachMod
