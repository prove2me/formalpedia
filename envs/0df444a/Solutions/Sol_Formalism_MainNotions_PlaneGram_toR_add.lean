-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.toR_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:28.890659+00:00
-- url     : https://prove2.me/submissions/77da75e7-bc44-4d8a-bdfc-adda1b56ff9c

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
theorem _root_.solution (x y : WithTop ℤ) : toR (x + y) = toR x + toR y := by
  induction x using WithTop.recTopCoe with
  | top => simp [toR_top]
  | coe m =>
    induction y using WithTop.recTopCoe with
    | top => simp [toR_top]
    | coe n =>
      rw [← WithTop.coe_add, toR_coe, toR_coe, toR_coe, ← WithTop.coe_add]
      push_cast; rfl
end Formalism.MainNotions.PlaneGram
