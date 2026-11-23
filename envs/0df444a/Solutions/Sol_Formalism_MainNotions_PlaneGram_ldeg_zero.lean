-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.ldeg_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:22.851792+00:00
-- url     : https://prove2.me/submissions/cfbae0d5-7b93-4514-a0d0-1531180826f8

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
theorem _root_.solution (i : L) : ldeg (0 : L × Fin r →₀ ℕ) i = 0 := by
  simp [ldeg]
end Formalism.MainNotions.PlaneGram
