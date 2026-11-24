-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.lord_C_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:07:48.682398+00:00
-- url     : https://prove2.me/submissions/966788ed-fb60-4922-874c-6af90ec4b297

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
theorem _root_.solution (a : R) : (0 : WithTop ℤ) ≤ lord (LaurentPolynomial.C a) := by
  rw [le_lord_iff]
  intro k hk
  rw [LaurentPolynomial.C_apply] at hk
  split_ifs at hk with h
  · rw [h]; exact le_refl _
  · exact absurd rfl hk
end Formalism.MainNotions.PlaneGram
