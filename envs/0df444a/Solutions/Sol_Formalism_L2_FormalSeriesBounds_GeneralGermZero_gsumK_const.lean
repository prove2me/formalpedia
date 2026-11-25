-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.GeneralGermZero.gsumK_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:17:38.12281+00:00
-- url     : https://prove2.me/submissions/c86d6017-4fa6-4bb0-803e-4ea0538bbf24

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GeneralGermZero_pairK_const
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_subst_zero


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
theorem _root_.solution {σ ι : Type} (Γ : ι → κ → MvPowerSeries σ C)
    (hΓ : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0) :
    ∀ (l : List ι) j, MvPowerSeries.constantCoeff (gsumK F Γ l j) = 0
  | [], j => by
    show MvPowerSeries.constantCoeff ((0 : κ → MvPowerSeries σ C) j) = 0
    simp
  | c :: l, j => constantCoeff_subst_zero (pairK_const (hΓ c) (solution Γ hΓ l)) (hF0 j)
end Formalism.L2.FormalSeriesBounds.GeneralGermZero
