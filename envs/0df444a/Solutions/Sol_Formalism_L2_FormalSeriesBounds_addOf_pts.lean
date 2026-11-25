-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.addOf_pts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:58:39.115946+00:00
-- url     : https://prove2.me/submissions/84c3b251-cfd4-4001-bb1d-66c369e940a7

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_pts_eq_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (F : Fin dd → PS C 2 dd) (j : Fin dd) :
    addOf F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) j = F j := by
  simp only [addOf, ev]
  rw [pts_eq_X, MvPowerSeries.subst_self]
  rfl
end Formalism.L2.FormalSeriesBounds
