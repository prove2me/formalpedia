-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.WachMod_d1_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:06.255189+00:00
-- url     : https://prove2.me/submissions/d18674cc-050d-412e-8fa8-43ec5560e7b0

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_DiffOneSmulOfTower

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
  {D' : Type} [AddCommGroup D'] [Module A D'] [Module O D'] [IsScalarTower O A D']
namespace Formalism.CoboundaryTransfers
theorem _root_.solution (W : WachMod B M D) (r : O) (y z : D) :
    W.d1 (r • y) (r • z) = r • W.d1 y z := by
  simp only [WachMod.d1, map_smul, smul_sub]
end Formalism.CoboundaryTransfers
