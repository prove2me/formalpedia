-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.bil_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:47:11.104608+00:00
-- url     : https://prove2.me/submissions/efdba345-ea2a-4a3a-b656-f215306d83c1

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum


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
variable {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {V : VF C} {F : PS C 2 dd} (hF : IntS V F) {w v : Fin dd → C} (hw : ∀ i, V.Ge 0 (w i))
    (hv : ∀ i, V.Ge 0 (v i)) : V.Ge 0 (bil F w v) :=
  VF.Ge.sum fun i _ => VF.Ge.sum fun j _ => (hF _).mul_int ((hw i).mul_int (hv j))
end Formalism.L2.FormalSeriesBounds
