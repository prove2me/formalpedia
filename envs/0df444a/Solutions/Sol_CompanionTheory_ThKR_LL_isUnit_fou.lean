-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.isUnit_fou
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:06.842122+00:00
-- url     : https://prove2.me/submissions/32fdf42a-220d-4fb5-bc03-011f3ff35a3d

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_HasDerivAtSchwartzToL2
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral
import Theorems.Thm_CompanionTheory_ThKR_LL_fou_mul_fouInv
import Theorems.Thm_CompanionTheory_ThKR_LL_fouInv_mul_fou

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
theorem _root_.solution : IsUnit (fou l) := ⟨⟨_, _, fou_mul_fouInv, fouInv_mul_fou⟩, rfl⟩
end CompanionTheory.ThKR.LL
