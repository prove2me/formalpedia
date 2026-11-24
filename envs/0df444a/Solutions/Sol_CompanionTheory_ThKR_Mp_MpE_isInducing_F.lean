-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.MpE.isInducing_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:22:42.396424+00:00
-- url     : https://prove2.me/submissions/497b9ec0-53b2-43a4-a960-6f4c394d22f7

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticGroupT2Space

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
variable {l : Type} [Fintype l] [DecidableEq l]
open MpE
open CompanionTheory.ThKR.Mp.MpE
namespace CompanionTheory.ThKR.Mp.MpE
theorem _root_.solution :
    IsInducing (fun g : G l => ((pr g, fun f => om g f) : Sp l × (L2 l → L2 l))) := ⟨rfl⟩
end CompanionTheory.ThKR.Mp.MpE
