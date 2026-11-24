-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.digitPart_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:51:07.059821+00:00
-- url     : https://prove2.me/submissions/1165ce59-14e2-474e-9615-2ea0ad27f866

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
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
variable (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (a : K) (F : MvPolynomial (D.OL × Fin D.r) K) :
    D.digitPart p ρ (a • F) = a • D.digitPart p ρ F := by
  simp only [digitPart_eq, map_smul]
end Formalism.MainNotions.PlaneGram.TwistData
