-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.sub_eOut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:08:39.208041+00:00
-- url     : https://prove2.me/submissions/f4963c75-b0ac-41c5-a1d5-9a9b572ba01a

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eIn_apply

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
theorem _root_.solution (α : L × Fin r →₀ ℕ) : α - eOut out α = eIn out α := by
  ext x; simp only [Finsupp.coe_tsub, Pi.sub_apply, eOut_apply, eIn_apply]; split_ifs <;> simp
end Formalism.MainNotions.PlaneGram
