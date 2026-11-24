-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.disjoint_eOut_eIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:07:36.337974+00:00
-- url     : https://prove2.me/submissions/fdfda18f-69cb-40d9-9acf-aee229c0bb6a

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
theorem _root_.solution {L : Type} {r : ℕ} (out : L → Prop) [DecidablePred out]
    (α β : L × Fin r →₀ ℕ) : Disjoint (eOut out α).support (eIn out β).support := by
  unfold eOut eIn
  rw [Finset.disjoint_left]
  intro x h1 h2
  rw [Finsupp.support_filter, Finset.mem_filter] at h1 h2
  exact h2.2 h1.2
end Formalism.MainNotions.PlaneGram
