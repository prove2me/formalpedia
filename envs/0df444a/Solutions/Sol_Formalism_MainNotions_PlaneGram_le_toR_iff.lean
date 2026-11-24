-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.le_toR_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:07:45.843449+00:00
-- url     : https://prove2.me/submissions/be3e8cea-325d-4ef2-9950-39baee657780

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_toR_top
import Theorems.Thm_Formalism_MainNotions_PlaneGram_toR_coe

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
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (θ : ℝ) (x : WithTop ℤ) :
    ((θ : ℝ) : WithTop ℝ) ≤ toR x ↔ ((⌈θ⌉ : ℤ) : WithTop ℤ) ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => simp [toR_top]
  | coe n => rw [toR_coe, WithTop.coe_le_coe, WithTop.coe_le_coe, Int.ceil_le]
end Formalism.MainNotions.PlaneGram
