-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.nxt_prv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:00:45.680492+00:00
-- url     : https://prove2.me/submissions/2c173b9e-86c7-4377-b3b7-dd56a1b5c84e

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SumOnLetterApplyInl
import Theorems.Thm_Formalism_MainNotions_PlaneGram_divE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_letE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.PlaneGram.divE_apply
attribute [local simp] Formalism.MainNotions.PlaneGram.letE_apply



set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable [CharZero K] (D : TwistData K) (v : AddValuation K (WithTop ℚ)) (p : ℕ)
variable {D v p}
variable (D p)
variable {D p}
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (D : TwistData K) (j : Fin D.J) : D.nxt (D.aux₃ j) = j := by
  apply Fin.ext
  have hJ : 0 < D.J := j.pos
  have hj := j.isLt
  simp only [nxt, aux₃]
  rw [Nat.mod_add_mod, show j.val + D.J - 1 + 1 = j.val + D.J by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt hj]
end Formalism.MainNotions.PlaneGram.TwistData
