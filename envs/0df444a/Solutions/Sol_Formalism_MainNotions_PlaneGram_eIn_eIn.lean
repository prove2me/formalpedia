-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.eIn_eIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:17:03.787545+00:00
-- url     : https://prove2.me/submissions/f7df14af-6ce8-443f-bfd8-87e8018831d7

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
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
theorem _root_.solution (α : L × Fin r →₀ ℕ) : eIn out (eIn out α) = eIn out α := by
  ext x; simp only [eIn_apply]; split_ifs <;> rfl
end Formalism.MainNotions.PlaneGram
