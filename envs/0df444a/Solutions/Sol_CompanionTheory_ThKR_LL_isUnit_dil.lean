-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.isUnit_dil
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:26:41.845672+00:00
-- url     : https://prove2.me/submissions/4ab8f3f1-91cf-49a0-b264-1213e76d0476

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_HasDerivAtSchwartzToL2
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral
import Theorems.Thm_CompanionTheory_ThKR_LL_dil_one
import Theorems.Thm_CompanionTheory_ThKR_LL_dil_mul

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
theorem _root_.solution {B : Eu l →L[ℝ] Eu l} (h : IsUnit B) : IsUnit (dil B) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨⟨dil u, dil (u⁻¹ : (Eu l →L[ℝ] Eu l)ˣ), by rw [dil_mul u.isUnit u⁻¹.isUnit, Units.inv_mul, dil_one],
    by rw [dil_mul u⁻¹.isUnit u.isUnit, Units.mul_inv, dil_one]⟩, rfl⟩
end CompanionTheory.ThKR.LL
