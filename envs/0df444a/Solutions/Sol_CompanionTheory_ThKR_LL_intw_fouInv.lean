-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.intw_fouInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:27.76529+00:00
-- url     : https://prove2.me/submissions/6e983337-6463-49cd-8630-e904bf968c01

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_HasDerivAtSchwartzToL2
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral
import Theorems.Thm_CompanionTheory_ThKR_LL_intw_fou

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
theorem _root_.solution (p q : Eu l) : Intw (fouInv l) p q q (-p) := fun f g h => by
  funext x
  have h1 := congrFun (intw_fou p q f g h) (-x)
  have e : ∀ (u : Sch l) y, fouInv l u y = fou l u (-y) := fun u y => rfl
  rw [e, h1]
  simp only [rf, e, inner_neg_left, inner_neg_right, neg_add]
end CompanionTheory.ThKR.LL
