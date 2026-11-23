-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.WachMod.mem_cocycles_of_isOneCocycle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:05.43626+00:00
-- url     : https://prove2.me/submissions/d223010a-8dfb-45fd-80ac-eebdc710b176

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_mem_Z1_iff_cocycle

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
theorem _root_.solution {y z : D} (h : W.Cocycle y z) : (y, z) ∈ W.Z1 :=
  (W.mem_Z1_iff_cocycle y z).2 h.2
end Formalism.CoboundaryTransfers.WachMod
