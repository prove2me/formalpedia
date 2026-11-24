-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.MpE.exists_sch_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:23:57.094634+00:00
-- url     : https://prove2.me/submissions/0f55eb28-86af-4dff-bec5-d000b06087f6

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticGroupT2Space
import Theorems.Thm_CompanionTheory_ThKF_E_exists_ne_zero
import Theorems.Thm_GlobalTheory_RealWeil_schwartzToL2_apply


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
open CompanionTheory.ThKR.Mp.MpE
namespace CompanionTheory.ThKR.Mp.MpE
theorem _root_.solution : ∃ f : Sch l, schwartzToL2 l f ≠ 0 := by
  obtain ⟨φ, hφ⟩ := exists_ne_zero (l := l) 0
  refine ⟨φ, fun h => hφ ?_⟩
  have : φ = 0 := injective_toLp 2 volume
    (show φ.toLp 2 volume = (0 : Sch l).toLp 2 volume by
      rw [← schwartzToL2_apply, ← schwartzToL2_apply, h, map_zero])
  simp [this]
end CompanionTheory.ThKR.Mp.MpE
