-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.divE_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:18:09.326834+00:00
-- url     : https://prove2.me/submissions/937cd752-a267-474b-a378-6e8accd3d397

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial

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
variable [CharZero K] (v : AddValuation K (WithTop ℚ)) (p : ℕ)
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {r : ℕ} (P : ℕ) (η : Fin r →₀ ℕ) (a : Fin r) : divE P η a = η a / P := rfl
end Formalism.MainNotions.PlaneGram
