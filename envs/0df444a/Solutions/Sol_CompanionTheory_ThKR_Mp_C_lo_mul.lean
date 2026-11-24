-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.C.lo_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:21:20.946082+00:00
-- url     : https://prove2.me/submissions/f197ac94-af29-42ac-9aab-ebeae659d733

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MapOfRealMul

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
open scoped Real
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open C
open CompanionTheory.ThKR.Mp.C
namespace CompanionTheory.ThKR.Mp.C
theorem _root_.solution (t : ℝ) : lo (l := l) t * lo (-t) = 1 := by
  rw [lo, lo, fromBlocks_multiply]
  simp
end CompanionTheory.ThKR.Mp.C
