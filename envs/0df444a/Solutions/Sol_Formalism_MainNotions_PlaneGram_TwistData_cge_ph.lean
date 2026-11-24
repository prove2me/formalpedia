-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.cge_ph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:38:53.254832+00:00
-- url     : https://prove2.me/submissions/ba8c332d-bdd6-4cf7-996a-8d253484b960

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ph_eq_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_sum


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
theorem _root_.solution (v : AddValuation K (WithTop ℚ)) (p : ℕ) {a : ℝ} {Z : MvPolynomial (D.ML × Fin D.r) K}
    (hZ : cge v a Z) : cge v a (D.ph p Z) := by
  rw [ph_eq_sum]
  exact cge_sum v _ _ fun ζ _ => cge_monomial v _ (hZ ζ)
end Formalism.MainNotions.PlaneGram.TwistData
