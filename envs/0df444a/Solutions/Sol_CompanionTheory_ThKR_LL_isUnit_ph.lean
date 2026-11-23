-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.isUnit_ph
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:23.439801+00:00
-- url     : https://prove2.me/submissions/c9fcc179-8c0e-4155-8ef4-d8b31a47bbeb

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_HasDerivAtSchwartzToL2
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral
import Theorems.Thm_CompanionTheory_ThKR_LL_ph_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_ph_zero

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
theorem _root_.solution (S : Eu l →L[ℝ] Eu l) : IsUnit (ph S) :=
  ⟨⟨ph S, ph (-S), by rw [ph_mul, add_neg_cancel, ph_zero], by rw [ph_mul, neg_add_cancel, ph_zero]⟩, rfl⟩
end CompanionTheory.ThKR.LL
