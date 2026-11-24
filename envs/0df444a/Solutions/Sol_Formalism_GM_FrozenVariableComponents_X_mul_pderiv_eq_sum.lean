-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.X_mul_pderiv_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:07.632799+00:00
-- url     : https://prove2.me/submissions/b917b8e1-0797-4560-9aaa-a3cf532c06a0

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_X_mul_monomial__a165fb611689

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
variable {K : Type*} [CommRing K] {σ : Type*}
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution [DecidableEq σ] (a b : σ) (F : MvPolynomial σ K) :
    X a * pderiv b F = ∑ m0 ∈ F.support,
      monomial (m0 - Finsupp.single b 1 + Finsupp.single a 1) (coeff m0 F * m0 b) := by
  conv_lhs => rw [F.as_sum]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m0 _ => ?_)
  rw [pderiv_monomial, X_mul_monomial']
end Formalism.GM.FrozenVariableComponents
