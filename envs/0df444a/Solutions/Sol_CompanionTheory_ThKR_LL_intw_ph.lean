-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.intw_ph
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:10.290468+00:00
-- url     : https://prove2.me/submissions/95e13e1a-9dd1-4c78-805c-2d9101b63ae6

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_HasDerivAtSchwartzToL2
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral
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
theorem _root_.solution {S : Eu l →L[ℝ] Eu l} (hS : ∀ x y, ⟪x, S y⟫ = ⟪y, S x⟫) (p q : Eu l) : Intw (ph S) p q p (q + S p) :=
  fun f g h => by
    funext x
    simp only [rf, ph_apply, h, ← mul_assoc, ← Complex.exp_add]
    congr 2
    rw [← add_mul, ← add_mul, ← ofReal_add, ← ofReal_add]
    congr 2
    simp only [inner_add_left, inner_add_right, map_add, hS p x, real_inner_comm x (S p)]
    ring
end CompanionTheory.ThKR.LL
