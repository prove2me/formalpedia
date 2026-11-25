-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.SelfConjPoints.inV_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:51:13.288119+00:00
-- url     : https://prove2.me/submissions/04fa6a33-7843-442e-b8de-58abb930e0b2

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RescaleInV
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_subst_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.SelfConjPoints
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
namespace Formalism.L2.FormalSeriesBounds.SelfConjPoints
theorem _root_.solution (j : Fin 2) {f : PowerSeries C} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (inV j f) = 0 :=
  constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) hf
end Formalism.L2.FormalSeriesBounds.SelfConjPoints
