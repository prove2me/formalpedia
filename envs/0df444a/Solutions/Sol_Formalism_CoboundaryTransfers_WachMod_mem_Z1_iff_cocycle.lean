-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.WachMod.mem_Z1_iff_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:49.88579+00:00
-- url     : https://prove2.me/submissions/7c3ef093-c566-4cb7-9330-d23c504659f0

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
theorem _root_.solution (y z : D) : (y, z) ∈ W.Z1 ↔ W.d1 y z = 0 := by
  rw [Z1, LinearMap.mem_ker, LinearMap.coprod_apply]
  simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.id_apply, d1]
  rw [← sub_eq_add_neg]
end Formalism.CoboundaryTransfers.WachMod
