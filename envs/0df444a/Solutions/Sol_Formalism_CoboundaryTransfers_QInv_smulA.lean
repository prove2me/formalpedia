-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.QInv_smulA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:04.941929+00:00
-- url     : https://prove2.me/submissions/5e22fbff-0cf4-4200-9839-28b479d6903c

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_TorsionKilledCriterionHolds

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
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
namespace Formalism.CoboundaryTransfers
theorem _root_.solution (W : WachMod B M D) (b : A) {y : D} (hy : W.QInv y) : W.QInv (b • y) := by
  show B.Q ^ M • (b • y) ∈ W.N
  rw [smul_comm]
  exact W.N.smul_mem b hy
end Formalism.CoboundaryTransfers
