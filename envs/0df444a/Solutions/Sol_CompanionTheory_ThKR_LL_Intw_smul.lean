-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.Intw.smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:45.852491+00:00
-- url     : https://prove2.me/submissions/f383be08-b969-4129-9312-a0f2d01361a8

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_HasDerivAtSchwartzToL2
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral

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
namespace Intw
theorem _root_.solution {S : Sch l →L[ℂ] Sch l} {p q p' q' : Eu l} (hS : Intw S p q p' q') (c : ℂ) :
    Intw (c • S) p q p' q' := fun f g h => by
  funext x
  have := congrFun (hS f g h) x
  simp only [rf, ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, smul_eq_mul] at this ⊢
  rw [this]
  ring
end Intw
end CompanionTheory.ThKR.LL
