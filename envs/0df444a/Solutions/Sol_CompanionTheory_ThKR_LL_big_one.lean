-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.big_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:53.195522+00:00
-- url     : https://prove2.me/submissions/9f23b4a6-b804-406b-8d41-a338ef1e4da3

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_HasDerivAtSchwartzToL2
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral
import Theorems.Thm_CompanionTheory_ThKR_LL_ph_zero
import Theorems.Thm_CompanionTheory_ThKR_LL_dil_one
import Theorems.Thm_CompanionTheory_ThKR_LL_fou_mul_fouInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.LL
variable {l : Type} [Fintype l]
namespace CompanionTheory.ThKR.LL
theorem _root_.solution : big (1 : Eu l →L[ℝ] Eu l) 0 0 1 = 1 := by
  simp [big, ph_zero, dil_one, fou_mul_fouInv]
end CompanionTheory.ThKR.LL
