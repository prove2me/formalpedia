-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.C.map_ofReal_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:21:22.156457+00:00
-- url     : https://prove2.me/submissions/b8acb4ea-331e-4cb8-94ad-862be8849e25

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
open CompanionTheory.ThKR.Mp.C
namespace CompanionTheory.ThKR.Mp.C
theorem _root_.solution (M N : Matrix l l ℝ) :
    (M * N).map Complex.ofReal = M.map Complex.ofReal * N.map Complex.ofReal := by
  ext i j
  simp [Matrix.mul_apply]
end CompanionTheory.ThKR.Mp.C
