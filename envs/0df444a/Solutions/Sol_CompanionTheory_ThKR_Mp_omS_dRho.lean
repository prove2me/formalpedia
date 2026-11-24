-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.omS_dRho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:25:54.427661+00:00
-- url     : https://prove2.me/submissions/212e9a33-07b7-4698-aaee-e78497ba442f

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_LocalLift
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Theorems.Thm_CompanionTheory_ThKR_Mp_mem
import Theorems.Thm_CompanionTheory_ThKF_E_Impl_dRho


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
theorem _root_.solution (g : G l) (w : l ⊕ l → ℝ) (f : Sch l) : omS g (dRho w f) = dRho ((pr g).1 *ᵥ w) (omS g f) :=
  (mem g).dRho w f
end CompanionTheory.ThKR.Mp
