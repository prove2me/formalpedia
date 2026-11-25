-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.uncurry_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:14:30.396342+00:00
-- url     : https://prove2.me/submissions/6bb70e81-9f2b-4dd1-a18b-6ef9111b6941

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_hasSubst_snd
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_uncurry_eq_subst
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
theorem _root_.solution (i : Fin dd) : un1 (MvPowerSeries.X ((0 : Fin 1), i) : PS C 1 dd) = MvPowerSeries.X i := by
  rw [uncurry_eq_subst, MvPowerSeries.subst_X hasSubst_snd]
end Formalism.L2.FormalSeriesBounds
