-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.exlg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:42:27.273595+00:00
-- url     : https://prove2.me/submissions/e2abcd8c-47b5-4b53-b148-45b2c4249bb8

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PullbackLogCoordsEvalZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_l
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_uncurry
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_uncurry_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_uncurry_comp


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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
variable (Y : FBChart C V O dd)
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution (n : Fin dd) : MvPowerSeries.subst (l Y) (e Y n) = MvPowerSeries.X n := by
  have ha : ∀ i, MvPowerSeries.constantCoeff (Y.lg i) = 0 := fun i => by
    rw [← constantCoeff_uncurry]; exact cc_l Y i
  show MvPowerSeries.subst (fun j => un1 (Y.lg j)) (un1 (Y.ex n)) = _
  rw [uncurry_comp ha, Y.ex_lg]
  exact uncurry_X n
end Formalism.L2.FormalSeriesBounds.VP
