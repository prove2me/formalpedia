-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.toR_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:41:22.113798+00:00
-- url     : https://prove2.me/submissions/02ea723e-bbd5-499f-98d4-3afcb083d56f

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
theorem _root_.solution {x y : WithTop ℤ} (h : x ≤ y) : toR x ≤ toR y := by
  induction y using WithTop.recTopCoe with
  | top => simp [toR_top]
  | coe n =>
    induction x using WithTop.recTopCoe with
    | top => exact absurd h (by simp)
    | coe m =>
      rw [toR_coe, toR_coe, WithTop.coe_le_coe]
      exact_mod_cast WithTop.coe_le_coe.mp h
end Formalism.MainNotions.PlaneGram
