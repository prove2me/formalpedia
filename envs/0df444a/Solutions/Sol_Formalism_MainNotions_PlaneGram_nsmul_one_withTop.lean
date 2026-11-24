-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.nsmul_one_withTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:08:33.416909+00:00
-- url     : https://prove2.me/submissions/8071218c-dab5-4914-be44-ae7527b2210e

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral

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
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (e : ℕ) : e • (1 : WithTop ℚ) = ((e : ℚ) : WithTop ℚ) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [succ_nsmul, ih]
    norm_cast
end Formalism.MainNotions.PlaneGram
