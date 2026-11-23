-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.eOut_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:52:28.538003+00:00
-- url     : https://prove2.me/submissions/7f0e12d4-7c80-450f-b6c9-32bbfdc2a1e2

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {L : Type} {r : ℕ} (out : L → Prop) [DecidablePred out]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (α β : L × Fin r →₀ ℕ) : eOut out (α + β) = eOut out α + eOut out β :=
  Finsupp.filter_add
end Formalism.MainNotions.PlaneGram
