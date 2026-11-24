-- Prove2me | solution 1 for Formalism.REAL.sumOfSquaresIdentity_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:43:10.670872+00:00
-- url     : https://prove2.me/submissions/a4d8426c-58bd-4622-b0b2-39bd506350e5

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SumOfSquaresIdentityHolds
import Theorems.Thm_Formalism_REAL_WDA_sgn_symm
import Theorems.Thm_Formalism_REAL_WDA_norm
import Theorems.Thm_Formalism_REAL_WDA_op

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : SumSq := by
  intro V _ _ n ε E w hU
  rw [WDA_op]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    inner_sum, inner_smul_right]
  simp only [Complex.ofReal_sum]
  simp only [WDA_norm hU]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [WDA_sgn_symm]
end Formalism.REAL
