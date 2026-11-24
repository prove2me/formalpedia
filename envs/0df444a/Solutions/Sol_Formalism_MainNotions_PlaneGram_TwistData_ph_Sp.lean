-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.ph_Sp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:38:53.928593+00:00
-- url     : https://prove2.me/submissions/1a39be77-4fd6-482d-a85b-08eae265fa40

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_phE_splitE
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ph_eq_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ph_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lsup_apply


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
theorem _root_.solution (p : ℕ) (Z : MvPolynomial (D.ML × Fin D.r) K) : D.ph p (D.Sp p Z) = D.ph p Z := by
  rw [Sp, lsup_apply, map_sum, ph_eq_sum]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [map_smul, ph_monomial, phE_splitE, smul_monomial, smul_eq_mul, mul_one]
end Formalism.MainNotions.PlaneGram.TwistData
