-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.ph_mem_PolK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:38:54.698745+00:00
-- url     : https://prove2.me/submissions/67f681ec-8281-4700-81ce-8364a5c04175

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ph_eq_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_monomial_mem_PolK
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ldeg_phE


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
theorem _root_.solution (p : ℕ) {Z : MvPolynomial (D.ML × Fin D.r) K} (hZ : D.Good p Z) :
    D.ph p Z ∈ PolK K D.r D.dO := by
  rw [ph_eq_sum]
  exact Submodule.sum_mem _ fun ζ hζ => monomial_mem_PolK _ _ _ (D.ldeg_phE p ζ (hZ ζ hζ))
end Formalism.MainNotions.PlaneGram.TwistData
