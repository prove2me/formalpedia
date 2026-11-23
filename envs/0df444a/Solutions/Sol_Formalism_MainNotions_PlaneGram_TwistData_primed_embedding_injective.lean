-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.primed_embedding_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:15.545938+00:00
-- url     : https://prove2.me/submissions/e91eb004-f1c9-4512-9f2f-2b54b9439ce4

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock

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
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution : Function.Injective D.aux₃ := by
  have key : ∀ a : Fin D.J, (a.val + D.J - 1) % D.J = if a.val = 0 then D.J - 1 else a.val - 1 := by
    intro a
    have := a.isLt
    split_ifs with h
    · rw [h, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [show a.val + D.J - 1 = (a.val - 1) + D.J by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
  intro a b h
  have e : (a.val + D.J - 1) % D.J = (b.val + D.J - 1) % D.J := congrArg Fin.val h
  rw [key a, key b] at e
  apply Fin.ext
  have := a.isLt
  have := b.isLt
  split_ifs at e <;> omega
end Formalism.MainNotions.PlaneGram.TwistData
