-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FormalGermZero.gsum_lg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:22:57.963407+00:00
-- url     : https://prove2.me/submissions/e329ab67-e66c-436c-95ec-ae1cd6591ae2

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_subst_zero_of_const
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_lg_addS
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_gsum_const
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_lg_const
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_uncurry


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
variable {dd : ℕ}
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O]
namespace Formalism.L2.FormalSeriesBounds.FormalGermZero
theorem _root_.solution {σ ι : Type} (Y : FBChart C V O dd) (Γ : ι → Fin dd → MvPowerSeries σ C)
    (hΓ : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0) (i : Fin dd) :
    ∀ l : List ι, MvPowerSeries.subst (gsum Y.B.G.F Γ l) (un1 (Y.lg i)) =
      (l.map fun c => MvPowerSeries.subst (Γ c) (un1 (Y.lg i))).sum
  | [] => by
    rw [List.map_nil, List.sum_nil]
    exact subst_zero_of_const _ (by rw [constantCoeff_uncurry, Y.lg_const])
  | c :: l => by
    rw [List.map_cons, List.sum_cons, ← solution Y Γ hΓ i l]
    exact lg_addS Y (Γ c) (gsum Y.B.G.F Γ l) (hΓ c) (gsum_const Y Γ hΓ l) i
end Formalism.L2.FormalSeriesBounds.FormalGermZero
