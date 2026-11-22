-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.lord_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:40:03.926592+00:00
-- url     : https://prove2.me/submissions/8119dcd4-22da-4556-9cbf-dbda9e971ae6

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_le_lord_iff

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
variable {R : Type} [Semiring R]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution : lord (0 : LaurentPolynomial R) = ⊤ := by
  rw [eq_top_iff, le_lord_iff]
  intro k hk
  exact absurd rfl hk
end Formalism.MainNotions.PlaneGram
