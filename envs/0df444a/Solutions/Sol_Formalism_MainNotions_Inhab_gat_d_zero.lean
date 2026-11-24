-- Prove2me | solution 1 for Formalism.MainNotions.Inhab.gat_d_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:40:12.291584+00:00
-- url     : https://prove2.me/submissions/90ad3b61-8be6-4e4b-bf98-e009074bec6b

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_SharpRestriction_InertJacobiLevels_ExtraGat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Inhab
open Formalism.MainNotions.G MvPolynomial
variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
variable (P : Places p O Kf)
namespace Formalism.MainNotions.Inhab
theorem _root_.solution (G : GAtP p) (h : G.M = ⊥) : G.d = 0 := by
  unfold GAtP.d
  rw [h]
  exact finrank_bot _ _
end Formalism.MainNotions.Inhab
