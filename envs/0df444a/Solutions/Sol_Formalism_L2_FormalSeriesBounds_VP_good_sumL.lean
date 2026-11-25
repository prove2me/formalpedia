-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.good_sumL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:23:29.773598+00:00
-- url     : https://prove2.me/submissions/1c5315ab-fb41-40bf-b87b-708994000522

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfBiadditiveCross
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstPartialLawAtPoints
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_GoodPt_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_GoodPt_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_add
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero


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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}
variable (Y : FBChart C V O dd)
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution : ∀ l : List (Fin dd → MvPowerSeries τ C), (∀ a ∈ l, GoodPt V a) → GoodPt V (sumL Y l)
  | [], _ => GoodPt.zero
  | a :: l, h => (h a List.mem_cons_self).add Y (solution l fun b hb => h b (List.mem_cons_of_mem _ hb))
end Formalism.L2.FormalSeriesBounds.VP
