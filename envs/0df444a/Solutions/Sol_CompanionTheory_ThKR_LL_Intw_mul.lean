-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.Intw.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:07.315802+00:00
-- url     : https://prove2.me/submissions/03a8a357-465b-4136-a980-cd044d1732a2

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
theorem _root_.solution {S T : Sch l →L[ℂ] Sch l} {p q p' q' p'' q'' : Eu l} (hS : Intw S p' q' p'' q'') (hT : Intw T p q p' q') :
    Intw (S * T) p q p'' q'' := fun f g h => hS _ _ (hT f g h)
end Intw
end CompanionTheory.ThKR.LL
