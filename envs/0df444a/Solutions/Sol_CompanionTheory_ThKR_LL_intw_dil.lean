-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.intw_dil
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:54.197943+00:00
-- url     : https://prove2.me/submissions/0bf8cd0b-12c5-41ca-a27f-ddacd8709761

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_HasDerivAtSchwartzToL2
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral
import Theorems.Thm_CompanionTheory_ThKR_LL_dil_apply

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
theorem _root_.solution {B : Eu l →L[ℝ] Eu l} (hB : IsUnit B) {p q p' q' : Eu l} (hp : B p' = p) (hq : ∀ x, ⟪q', x⟫ = ⟪q, B x⟫) :
    Intw (dil B) p q p' q' := fun f g h => by
  funext x
  simp only [rf, dil_apply hB, h, map_add, hp, real_inner_comm q' p', hq, real_inner_comm q p]
end CompanionTheory.ThKR.LL
