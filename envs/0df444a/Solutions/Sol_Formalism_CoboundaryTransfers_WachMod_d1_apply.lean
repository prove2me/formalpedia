-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.WachMod.d1_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:16:53.674852+00:00
-- url     : https://prove2.me/submissions/f64f9700-5eed-4c22-85d6-be2f2b47da3b

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
theorem _root_.solution (y z : D) : W.d1 y z = (W.γ y - y) - (W.φ z - z) := rfl
end Formalism.CoboundaryTransfers.WachMod
