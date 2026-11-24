-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.pullL_coefOut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:33:14.396305+00:00
-- url     : https://prove2.me/submissions/b7889db4-6b45-48a1-bafe-95e0e0116782

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_RenamePullLCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_pullE_eIn
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lsup_monomial


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
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (μ : D.EM) (Z : MvPolynomial (D.ML × Fin D.r) K) :
    D.pullL j (coefOut (D.outSeg j) μ Z) =
      ∑ α ∈ Z.support, if eOut (D.outSeg j) α = μ then monomial (D.pullE j α) (Z.coeff α) else 0 := by
  unfold coefOut
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · rw [pullL, lsup_monomial, pullE_eIn, smul_monomial, smul_eq_mul, mul_one]
  · rw [map_zero]
end Formalism.MainNotions.PlaneGram.TwistData
