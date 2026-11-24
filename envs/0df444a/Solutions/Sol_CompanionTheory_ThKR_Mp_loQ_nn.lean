-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.loQ_nn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:21:21.404093+00:00
-- url     : https://prove2.me/submissions/15a82214-a82a-4a3a-bf34-e2fcfed8ea2c

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticUnipotentBlockSecondDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace CompanionTheory.ThKR.Mp
theorem _root_.solution (S : Matrix l l ℝ) (t : ℝ) (s : Mat l) : loQ (nn S t * s) = loQ s := by
  ext a b
  simp [loQ, nn, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
end CompanionTheory.ThKR.Mp
