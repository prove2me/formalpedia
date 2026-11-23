-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.iso_ph
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:09.30166+00:00
-- url     : https://prove2.me/submissions/74477d2e-6350-4c4c-915b-66ddf9cc9705

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_HasDerivAtSchwartzToL2
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral
import Theorems.Thm_CompanionTheory_ThKR_LL_iso_of_integral
import Theorems.Thm_CompanionTheory_ThKR_LL_ph_apply

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
theorem _root_.solution (S : Eu l →L[ℝ] Eu l) : Iso (ph S) := iso_of_integral fun f => by
  simp only [ph_apply, norm_mul, norm_exp_ofReal_mul_I, one_mul]
end CompanionTheory.ThKR.LL
