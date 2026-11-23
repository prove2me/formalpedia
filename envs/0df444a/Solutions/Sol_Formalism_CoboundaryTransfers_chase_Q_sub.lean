-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.chase_Q_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:15.121821+00:00
-- url     : https://prove2.me/submissions/404f43dd-1cc1-4226-94cf-442668d72b81

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
theorem _root_.solution (W : WachMod B M D) {x y : D} (hx : W.QInv x) (hy : W.QInv y) :
    W.QInv (x - y) := by
  show B.Q ^ M • (x - y) ∈ W.N
  rw [smul_sub]
  exact W.N.sub_mem hx hy
end Formalism.CoboundaryTransfers
