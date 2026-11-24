-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.eOut_add_eIn_n
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:07:38.391422+00:00
-- url     : https://prove2.me/submissions/a54be666-0177-40b9-bbdd-d573dfe53a87

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
theorem _root_.solution {L : Type} {r : ℕ} (out : L → Prop) [DecidablePred out] (α : L × Fin r →₀ ℕ) :
    eOut out α + eIn out α = α := by
  unfold eOut eIn
  exact Finsupp.filter_pos_add_filter_neg α _
end Formalism.MainNotions.PlaneGram
