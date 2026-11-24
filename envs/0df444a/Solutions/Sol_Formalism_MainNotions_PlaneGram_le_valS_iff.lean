-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.le_valS_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:27:02.536839+00:00
-- url     : https://prove2.me/submissions/265364e9-2d3e-4435-9a29-f8c1d675f84f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_pge_iff_inf

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
    n ≤ valS sg S F ↔ ∀ β, n ≤ lord ((subV sg S F).coeff β) := by
  unfold valS
  exact pge_iff_inf n _
end Formalism.MainNotions.PlaneGram
