-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.weyl_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:02:27.924868+00:00
-- url     : https://prove2.me/submissions/4422f6ee-bd4e-4435-8620-bc8d096bce94

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaDef
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_HasDerivAtSchwartzToL2
import Theorems.Thm_CompanionTheory_ThKR_LL_csmul
import Theorems.Thm_CompanionTheory_ThKF_E_Impl_dRho
import Theorems.Thm_GlobalTheory_RealWeil_dRho_eq_sum


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
open scoped Real
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.LL
variable {l : Type} [Fintype l]
variable [DecidableEq l]
namespace CompanionTheory.ThKR.LL
theorem _root_.solution {V : Sch l →L[ℂ] Sch l} {w v : l ⊕ l → ℝ} (h : ∀ f, dRho w (V f) = V (dRho v f))
    (A : Sch l →L[ℂ] Sch l) (f : Sch l) :
    schwartzToL2 l ((A * dRho w) (V f)) = ∑ a, v a • schwartzToL2 l (A (V (dRho (Pi.single a 1) f))) := by
  rw [ContinuousLinearMap.mul_apply, h, dRho_eq_sum v]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul]
  simp only [csmul]
end CompanionTheory.ThKR.LL
