-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.GeneralGermZero.gsumK_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:25:04.501699+00:00
-- url     : https://prove2.me/submissions/ff392f29-e4c3-4892-9576-c30e1d3fef9e

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GeneralGermZero_pairK_const
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GeneralGermZero_pairK_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GeneralGermZero_gsumK_const
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
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
theorem _root_.solution {V : VF C} (hFI : ∀ k, IntS V (F k)) {σ ι : Type} (Γ : ι → κ → MvPowerSeries σ C)
    (hΓ0 : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0) (hΓ : ∀ c j, IntS V (Γ c j)) :
    ∀ (l : List ι) j, IntS V (gsumK F Γ l j)
  | [], j => by
    intro μ
    show V.Ge 0 (MvPowerSeries.coeff μ ((0 : κ → MvPowerSeries σ C) j))
    rw [Pi.zero_apply, map_zero]
    exact VF.Ge.zero 0
  | c :: l, j => IntS.subst (pairK_const (hΓ0 c) (gsumK_const hF0 Γ hΓ0 l))
      (pairK_int (hΓ c) (solution hFI Γ hΓ0 hΓ l)) (hFI j)
end Formalism.L2.FormalSeriesBounds.GeneralGermZero
