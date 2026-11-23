-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.chase_Q_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:14.703929+00:00
-- url     : https://prove2.me/submissions/aeee18c5-ca39-41de-aef5-c0c40567d76f

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
theorem _root_.solution (W : WachMod B M D) (r : O) {x : D} (hx : W.QInv x) : W.QInv (r • x) := by
  show B.Q ^ M • (r • x) ∈ W.N
  rw [algebra_compatible_smul A r x, smul_comm (B.Q ^ M) (algebraMap O A r) x]
  exact W.N.smul_mem _ hx
end Formalism.CoboundaryTransfers
