-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.gaR_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:53:01.316971+00:00
-- url     : https://prove2.me/submissions/26993b92-90a2-45d7-b561-86f4df65ed6c

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CollapseExponent
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_PrimedEmbeddingInjective
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_substituted_exponent_eq_embedded

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
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (p : ℕ) (gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K) (ζ : D.EM) :
    D.gaR p gam (D.labF ζ) 1 ζ = D.gaP p gam ζ := by
  simp only [gaR, gaP, zpow_one, substituted_exponent_eq_embedded]
end Formalism.MainNotions.PlaneGram.TwistData
