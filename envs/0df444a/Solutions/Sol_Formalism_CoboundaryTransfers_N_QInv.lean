-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.N_QInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:50.827959+00:00
-- url     : https://prove2.me/submissions/de80f511-cb52-44c4-bc86-8e815e7c4505

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
theorem _root_.solution (W : WachMod B M D) {x : D} (hx : x ∈ W.N) : W.QInv x := W.N.smul_mem _ hx
end Formalism.CoboundaryTransfers
