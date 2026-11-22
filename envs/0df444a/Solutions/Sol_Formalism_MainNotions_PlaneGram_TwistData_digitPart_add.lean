-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.digitPart_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:48.439606+00:00
-- url     : https://prove2.me/submissions/ee8af4c5-bd42-4d57-882d-74e5066e6fc8

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
theorem _root_.solution (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (F G : MvPolynomial (D.OL × Fin D.r) K) :
    D.digitPart p ρ (F + G) = D.digitPart p ρ F + D.digitPart p ρ G := by
  simp only [digitPart_eq, map_add]
end Formalism.MainNotions.PlaneGram.TwistData
