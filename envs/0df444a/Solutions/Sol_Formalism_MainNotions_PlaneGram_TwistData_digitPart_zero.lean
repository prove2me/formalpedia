-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.digitPart_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:51:10.255526+00:00
-- url     : https://prove2.me/submissions/6f263e32-686d-4337-8312-a64fe99ca730

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_digitPart_eq


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
variable (D : TwistData K) (p : ℕ)
variable (t : D.Tau)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (ρ : D.Tau → Fin D.r → ℕ) :
    D.digitPart p ρ (0 : MvPolynomial (D.OL × Fin D.r) K) = 0 := by
  rw [digitPart_eq, map_zero]
end Formalism.MainNotions.PlaneGram.TwistData
