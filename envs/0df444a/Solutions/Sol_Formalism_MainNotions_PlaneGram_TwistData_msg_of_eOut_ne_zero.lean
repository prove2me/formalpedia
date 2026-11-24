-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.msg_of_eOut_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:07:38.512104+00:00
-- url     : https://prove2.me/submissions/1fb2b1b6-4b75-4f39-8f04-ea3d04440789

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyLabel
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_apply


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
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)
variable [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (ζ : D.EM) (i : D.ML) (a : Fin D.r) (h : eOut D.outP ζ (i, a) ≠ 0) :
    D.msg i = true := by
  rw [eOut_apply] at h
  split_ifs at h with hi
  · rcases i with b | t | t | t
    · simp [outP, outB] at hi
    · rfl
    · simp [outP, outB] at hi
    · rfl
  · exact absurd rfl h
end Formalism.MainNotions.PlaneGram.TwistData
