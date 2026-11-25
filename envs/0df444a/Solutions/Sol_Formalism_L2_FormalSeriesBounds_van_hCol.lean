-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.van_hCol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:35:35.815614+00:00
-- url     : https://prove2.me/submissions/15991aab-5835-461d-b736-1def95c9e68c

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePAxesSelfSt
import Theorems.Thm_P2M_RH_Formalism_L2_FormalSeriesBounds_van_X_02236d9c7e0fe878
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (col g : Fin 2) (h : PS C 2 dd)
    (hh : ∀ e : Fin 2 × Fin dd →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ g) → coeff e h = 0) :
    Van {w : Fin 2 × (Fin 2 × Fin dd) | w.1 = g} (hCol col h) := by
  unfold hCol
  refine Van.subst {s : Fin 2 × Fin dd | s.1 = g} (fun _ => constantCoeff_X _) ?_ ?_
  · intro s hs
    exact van_X hs
  · intro e he
    exact hh e he
end Formalism.L2.FormalSeriesBounds
