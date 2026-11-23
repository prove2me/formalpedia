-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.WachMod.qInv_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:05.713125+00:00
-- url     : https://prove2.me/submissions/f26d6694-54cd-4b4f-bbd1-e850f5b0f1ce

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
theorem _root_.solution {y y' : D} (hy : W.QInv y) (hy' : W.QInv y') : W.QInv (y - y') := by
  simp only [QInv, smul_sub]; exact W.N.sub_mem hy hy'
end Formalism.CoboundaryTransfers.WachMod
