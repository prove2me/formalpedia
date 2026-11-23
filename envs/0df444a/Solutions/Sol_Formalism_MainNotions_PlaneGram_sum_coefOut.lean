-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.sum_coefOut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:32.716263+00:00
-- url     : https://prove2.me/submissions/2b0a916f-b357-4cb1-bf0a-7e12af14f167

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_add_eIn
import Theorems.Thm_Formalism_MainNotions_PlaneGram_sum_mul_coefOut

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
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ}
  (out : L → Prop) [DecidablePred out]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (F : MvPolynomial (L × Fin r) K) :
    F = ∑ μ ∈ F.support.image (eOut out), monomial μ 1 * coefOut out μ F := by
  rw [sum_mul_coefOut out (fun μ => monomial μ 1) F]
  conv_lhs => rw [F.as_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [monomial_mul, eOut_add_eIn, one_mul]
end Formalism.MainNotions.PlaneGram
