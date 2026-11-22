-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.eIn_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:14:52.385137+00:00
-- url     : https://prove2.me/submissions/9fa36579-574a-4816-b9ab-705dc60821e5

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
variable {L : Type} {r : ℕ} (out : L → Prop) [DecidablePred out]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (α : L × Fin r →₀ ℕ) (x : L × Fin r) :
    eIn out α x = if out x.1 then 0 else α x := by
  unfold eIn; rw [Finsupp.filter_apply]
  by_cases h : out x.1 <;> simp [h]
end Formalism.MainNotions.PlaneGram
