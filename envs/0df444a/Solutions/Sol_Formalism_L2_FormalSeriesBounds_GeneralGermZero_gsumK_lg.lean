-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.GeneralGermZero.gsumK_lg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:27:11.115946+00:00
-- url     : https://prove2.me/submissions/3973a26d-d1c3-4f51-af9d-64029f0b14ea

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GeneralGermZero_lg_addK
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GeneralGermZero_gsumK_const
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_subst_zero_of_const
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
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
open Formalism.L2.FormalSeriesBounds.GeneralGermZero
open Formalism.IncomingBounds FormalGermZero
variable {C : Type} [Field C] {κ : Type} [Fintype κ]
variable {F : κ → MvPowerSeries (Fin 2 × κ) C} (hF0 : ∀ k, MvPowerSeries.constantCoeff (F k) = 0)
include hF0
namespace Formalism.L2.FormalSeriesBounds.GeneralGermZero
theorem _root_.solution {lg : κ → MvPowerSeries κ C} (hadd : LgAdd F lg) (hlg0 : ∀ k, MvPowerSeries.constantCoeff (lg k) = 0)
    {σ ι : Type} (Γ : ι → κ → MvPowerSeries σ C)
    (hΓ : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0) (i : κ) :
    ∀ l : List ι, MvPowerSeries.subst (gsumK F Γ l) (lg i) = (l.map fun c => MvPowerSeries.subst (Γ c) (lg i)).sum
  | [] => by
    rw [List.map_nil, List.sum_nil]
    exact subst_zero_of_const _ (hlg0 i)
  | c :: l => by
    rw [List.map_cons, List.sum_cons, ← solution hadd hlg0 Γ hΓ i l]
    exact lg_addK F hF0 lg hadd (Γ c) (gsumK F Γ l) (hΓ c) (gsumK_const hF0 Γ hΓ l) i
end Formalism.L2.FormalSeriesBounds.GeneralGermZero
