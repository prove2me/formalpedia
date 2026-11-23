-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.ldeg_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:22.891723+00:00
-- url     : https://prove2.me/submissions/bf4431ca-4837-4fa2-b68a-8632ba0136c0

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
variable {L : Type} {r : ℕ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (α β : L × Fin r →₀ ℕ) (i : L) : ldeg (α + β) i = ldeg α i + ldeg β i := by
  unfold ldeg
  simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]
end Formalism.MainNotions.PlaneGram
