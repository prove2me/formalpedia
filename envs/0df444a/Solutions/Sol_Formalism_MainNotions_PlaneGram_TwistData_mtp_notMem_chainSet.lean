-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.mtp_notMem_chainSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:07:40.542809+00:00
-- url     : https://prove2.me/submissions/dc523274-75a3-4af7-9cba-1315a7e4b5d6

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_mem_chainSet

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
theorem _root_.solution (j : Fin D.J) (i : Fin (D.nch j)) (t : D.Tau) :
    D.mtp t ∉ D.chainSet j i := by
  rw [D.mem_chainSet]
  rintro (⟨b, _, h⟩ | ⟨m, h⟩) <;> simp [mtp, mb, mw] at h
end Formalism.MainNotions.PlaneGram.TwistData
