-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.om_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:25:47.315595+00:00
-- url     : https://prove2.me/submissions/e805adce-29a3-4008-8c18-692a027d7f82

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_LocalLift
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Theorems.Thm_CompanionTheory_ThKR_Mp_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable (l : Type) [Fintype l] [DecidableEq l]
variable {l}
namespace CompanionTheory.ThKR.Mp
theorem _root_.solution (g : G l) (w : l ⊕ l → ℝ) (f : L2 l) : om g (rho w f) = rho ((pr g).1 *ᵥ w) (om g f) := (mem g).rho w f
end CompanionTheory.ThKR.Mp
