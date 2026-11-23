-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.chase_Q_smulA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:14.698947+00:00
-- url     : https://prove2.me/submissions/6897a991-f62f-4a80-85f5-004a30ffb352

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
theorem _root_.solution (W : WachMod B M D) (b : A) {x : D} (hx : W.QInv x) : W.QInv (b • x) := by
  show B.Q ^ M • (b • x) ∈ W.N
  rw [smul_comm (B.Q ^ M) b x]
  exact W.N.smul_mem b hx
end Formalism.CoboundaryTransfers
