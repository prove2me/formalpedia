-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.le_valS_iff_pge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:30:56.220001+00:00
-- url     : https://prove2.me/submissions/48d6a28b-0b44-4250-91b3-bbfa8269ca53

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_le_valS_iff

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
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L)
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (n : WithTop ℤ) (F : MvPolynomial (L × Fin r) K) :
    n ≤ valS sg S F ↔ pge n (subV sg S F) := le_valS_iff sg S n F
end Formalism.MainNotions.PlaneGram
