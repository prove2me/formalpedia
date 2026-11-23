-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.WachMod.diffOne_diffZero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:55.663227+00:00
-- url     : https://prove2.me/submissions/df7bba77-937b-4aae-81bc-d3c5b950e83a

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary

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
theorem _root_.solution (x : D) : W.d1 (W.φ x - x) (W.γ x - x) = 0 := by
  simp only [d1, map_sub, W.comm]; abel
end Formalism.CoboundaryTransfers.WachMod
