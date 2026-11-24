-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.ph_lin_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:32.170255+00:00
-- url     : https://prove2.me/submissions/6c2ac62d-8509-4db0-9d42-bd097e808f83

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lin_eq_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial


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
theorem _root_.solution (p : ℕ) (Z : MvPolynomial (D.ML × Fin D.r) K) :
    D.ph p Z = ∑ ζ ∈ Z.support, Z.coeff ζ • D.ph p (monomial ζ 1) :=
  lin_eq_sum (D.ph p).toLinearMap Z
end Formalism.MainNotions.PlaneGram.TwistData
