-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FormalGermZero.intS_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:58:30.374839+00:00
-- url     : https://prove2.me/submissions/cbc127cb-2f87-4da1-b029-ab3f565cb60a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AbstractGermZero_intS_iff_alt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_zero


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
open Formalism.L2.FormalSeriesBounds.FormalGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds.FormalGermZero
theorem _root_.solution {V : VF C} {τ : Type} (c : τ) : IntS V (MvPowerSeries.X c : MvPowerSeries τ C) := by
  rw [AbstractGermZero.intS_iff_alt]
  intro μ
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact AltInv.intC_one (v := V.v)
  · exact AltInv.intC_zero (v := V.v)
end Formalism.L2.FormalSeriesBounds.FormalGermZero
