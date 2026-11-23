-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.isUnit_fouInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:06.902489+00:00
-- url     : https://prove2.me/submissions/c22c9891-17af-4504-bd3c-6e7397ad5eed

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
theorem _root_.solution : IsUnit (fouInv l) := ⟨⟨_, _, fouInv_mul_fou, fou_mul_fouInv⟩, rfl⟩
end CompanionTheory.ThKR.LL
