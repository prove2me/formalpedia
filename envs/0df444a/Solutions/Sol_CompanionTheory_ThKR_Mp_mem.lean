-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:16:04.150676+00:00
-- url     : https://prove2.me/submissions/15697501-70c0-4fbe-8bc4-3ebf80d96956

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_LocalLift
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm

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
theorem _root_.solution (g : G l) : Mem (Subtype.val (p := (· ∈ sub l)) g) := Subtype.property (p := (· ∈ sub l)) g
end CompanionTheory.ThKR.Mp
